#include <fcntl.h>
#include <parlib/assert.h>
#include <parlib/common.h>
#include <parlib/debug.h>
#include <parlib/ros_debug.h>
#include <parlib/event.h>
#include <parlib/parlib.h>
#include <parlib/spinlock.h>
#include <parlib/vcore.h>
#include <ros/common.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

int akaros_printf(const char *format, ...)
{
	va_list ap;
	int ret;

	va_start(ap, format);
	ret = vprintf(format, ap);
	va_end(ap);
	return ret;
}

/* Poor man's Ftrace, won't work well with concurrency. */
static const char *blacklist[] = {
	"whatever",
};

static bool is_blacklisted(const char *s)
{
	for (int i = 0; i < COUNT_OF(blacklist); i++) {
		if (!strcmp(blacklist[i], s))
			return TRUE;
	}
	return FALSE;
}

static int tab_depth = 0;
static bool print = TRUE;

void reset_print_func_depth(void)
{
	tab_depth = 0;
}

void toggle_print_func(void)
{
	print = !print;
	printf("Func entry/exit printing is now %sabled\n", print ? "en" : "dis");
}

static spinlock_t lock = {0};

void __print_func_entry(const char *func, const char *file)
{
	if (!print)
		return;
	if (is_blacklisted(func))
		return;
	spinlock_lock(&lock);
	printd("Vcore %2d", vcore_id());	/* helps with multicore output */
	for (int i = 0; i < tab_depth; i++)
		printf("\t");
	printf("%s() in %s\n", func, file);
	spinlock_unlock(&lock);
	tab_depth++;
}

void __print_func_exit(const char *func, const char *file)
{
	if (!print)
		return;
	if (is_blacklisted(func))
		return;
	tab_depth--;
	spinlock_lock(&lock);
	printd("Vcore %2d", vcore_id());
	for (int i = 0; i < tab_depth; i++)
		printf("\t");
	printf("---- %s()\n", func);
	spinlock_unlock(&lock);
}

static void handle_debug_msg(struct syscall *sysc);
static void debug_read(int fd, void *buf, size_t len);
static int handle_one_msg(struct event_mbox *ev_mbox);
static void debug_read_handler(struct event_queue *ev_q);

static int debug_send_packet(int fd, struct d9_header *hdr);
static int debug_send_error(uint32_t errnum);
static struct d9_header *debug_read_packet(int fd);
static int read_all(int fd, void *data, size_t size);
static int check_error_packet(struct d9_header *hdr, enum d9_msg_t expected);

static int d9s_treadmem(struct d9_header *hdr, void *data);
static int d9s_tstoremem(struct d9_header *hdr, void *data);
static int d9s_tfetchreg(struct d9_header *hdr, void *data);
static int d9s_tstorereg(struct d9_header *hdr, void *data);
static int d9s_tresume(struct d9_header *hdr, void *data);

static int d9c_thitbreakpoint(struct d9_header *hdr);
static int d9c_taddthread(struct d9_header *hdr);

/* ev_q for read syscall on debug pipe. */
static struct event_queue *debug_read_ev_q;
static struct syscall debug_read_sysc;
static int debug_fd = -1;

/* async_read_buf is the buffer used to read the header of a packet.
 *
 * We can only have one of these reads at a time anyway. */
static char async_read_buf[sizeof(struct d9_header)];

/* d9_ops are user-supplied routines that fill in the response packet with the
 * appropriate information and/or do the requested operation. These may block.
 */
static struct d9_ops *d9_ops;

/* A message handler is an internal routine that allocates the appropriate
 * response packet and coordinates sending the appropriate response to
 * gdbserver. */
typedef int (*message_handler)(struct d9_header *hdr, void *data);
#define D9_HANDLER(x) (x - D9_TREADMEM)
static message_handler srv_msg_handlers[D9_HANDLER(D9_NUM_MESSAGES)];

typedef int (*clt_message_handler)(struct d9_header *hdr);
static clt_message_handler clt_msg_handlers[D9_HANDLER(D9_NUM_MESSAGES)];

/* queue_handle_one_message extracts one message from the mbox and calls the
 * appropriate handler for that message. */
static int queue_handle_one_msg(struct event_mbox *ev_mbox)
{
	struct event_msg msg;
	struct syscall *sysc;

	if (!extract_one_mbox_msg(ev_mbox, &msg))
		return 0;

	assert(msg.ev_type == EV_SYSCALL);
	sysc = msg.ev_arg3;
	assert(sysc);
	handle_debug_msg(sysc);
	return 1;
}

/* queue_read_handler is the event queue handler for the async read evq. */
static void queue_read_handler(struct event_queue *ev_q)
{
	assert(ev_q);
	assert(ev_q->ev_mbox);
	while (queue_handle_one_msg(ev_q->ev_mbox))
		;
}

void d9s_init(struct d9_ops *dops)
{
	int fd;
	int p[2];
	char buf[60];
	int ret;

	/* Set up parlib queue for asynchronous read notifications. */
	debug_read_ev_q = get_eventq(EV_MBOX_UCQ);
	debug_read_ev_q->ev_flags = EVENT_IPI | EVENT_INDIR | EVENT_SPAM_INDIR |
		EVENT_WAKEUP;
	debug_read_ev_q->ev_handler = queue_read_handler;

	/* Set up d9 handlers. */
	srv_msg_handlers[D9_HANDLER(D9_TREADMEM)] = d9s_treadmem;
	srv_msg_handlers[D9_HANDLER(D9_TSTOREMEM)] = d9s_tstoremem;
	srv_msg_handlers[D9_HANDLER(D9_TFETCHREG)] = d9s_tfetchreg;
	srv_msg_handlers[D9_HANDLER(D9_TSTOREREG)] = d9s_tstorereg;
	srv_msg_handlers[D9_HANDLER(D9_TRESUME)] = d9s_tresume;

	/* Set d9 ops. */
	d9_ops = dops;

	/* Open a pipe and post it in #srv.
	 * TODO(chrisko): add special file #proc/PID/debug that works like #srv.
	 */
	ret = pipe(p);
	if (ret < 0)
		panic("could not get pipe.");

	snprintf(buf, sizeof(buf), "#srv/debug-%d", getpid());
	fd = open(buf, O_WRONLY|O_CREAT, 0666);
	if (fd < 0)
		panic("could not open debug file.");

	snprintf(buf, sizeof(buf), "%d", p[1]);
	if (write(fd, buf, strlen(buf)) != strlen(buf))
		panic("could not write fd to debug file.");

	close(p[1]);

	debug_fd = p[0];
	debug_read(debug_fd, async_read_buf, sizeof(struct d9_header));
}

static void debug_read(int fd, void *buf, size_t len)
{
	memset(&debug_read_sysc, 0, sizeof(struct syscall));
	syscall_async(&debug_read_sysc, SYS_read, fd, buf, len);

	if (!register_evq(&debug_read_sysc, debug_read_ev_q))
		handle_debug_msg(&debug_read_sysc);
}

static void handle_debug_msg(struct syscall *sysc)
{
	struct d9_header *hdr;

	switch (sysc->retval) {
	case 0:
		panic("read syscall: got 0 bytes.");
		break;

	case -1:
		panic("read failed");
		break;

	default:
		if (sysc->retval != sizeof(struct d9_header))
			panic("2LS debug: should have received D9 header.");

		hdr = (struct d9_header *) sysc->arg1;

		/* Read the remaining bytes of the message. */
		size_t msg_size = hdr->size - sizeof(struct d9_header);
		void *data = NULL;

		if (msg_size > 0) {
			/* Read the remaining data of this packet. */
			data = calloc(msg_size, 1);
			if (data == NULL)
				panic("handle_debug_msg: calloc failed.");

			if (read_all(debug_fd, data, msg_size)) {
				free(data);
				panic("handle_debug_msg: read_all failed.");
			}
		}

		/* Call the appropriate handler for this packet. */
		if (srv_msg_handlers[D9_HANDLER(hdr->msg_type)] != NULL)
			srv_msg_handlers[D9_HANDLER(hdr->msg_type)](hdr, data);
		else
			panic("2LS debug: no message handler found.");

		if (data)
			free(data);

		debug_read(debug_fd, async_read_buf, sizeof(struct d9_header));
		break;
	}
}

/* alloc_packet allocates memory for a packet of given type. */
static struct d9_header *alloc_packet(size_t pck_len, enum d9_msg_t msg_type)
{
	struct d9_header *hdr;

	if (pck_len >= UINT32_MAX)
		panic("2LS debug: packet too long.");

	hdr = calloc(1, pck_len);
	if (hdr == NULL)
		return NULL;

	hdr->size = pck_len;
	hdr->msg_type = msg_type;
	return hdr;
}

/* d9s_read_memory is the d9_ops func called to fulfill a TREADMEM request. */
int d9s_read_memory(const struct d9_treadmem_msg *req,
                    struct d9_rreadmem_msg *resp)
{
	resp->length = req->length;
	/* TODO(chrisko): can check page tables to see whether this should actually
	 * succeed instead of letting it fault. */
	memcpy(resp->data, (void *) req->address, req->length);
	return 0;
}

/* d9s_store_memory is the d9_ops func called to fulfill a TSTOREMEM request. */
int d9s_store_memory(const struct d9_tstoremem_msg *req)
{
	/* TODO(chrisko): can check page tables to see whether this should actually
	 * succeed instead of letting it fault. */
	memcpy((void *) req->address, req->data, req->length);
	return 0;
}

/* d9s_resume is the d9_ops func called to fulfill a TRESUME request. */
void d9s_resume(bool singlestep)
{
	if (singlestep)
		uthread_apply_all(uthread_enable_single_step);
	else
		uthread_apply_all(uthread_disable_single_step);
	uthread_apply_all(uthread_runnable);
}

int d9s_notify_hit_breakpoint(uint64_t tid, uint64_t address)
{
	struct d9_thitbreakpoint thb =
		D9_INIT_HDR(sizeof(struct d9_thitbreakpoint), D9_THITBREAKPOINT);

	if (debug_fd == -1)
		return 0;

	thb.msg.pid = getpid();
	thb.msg.tid = tid;
	thb.msg.address = address;

	return debug_send_packet(debug_fd, &(thb.hdr));
}

int d9s_notify_add_thread(uint64_t tid)
{
	struct d9_taddthread tat =
		D9_INIT_HDR(sizeof(struct d9_taddthread), D9_TADDTHREAD);

	if (debug_fd == -1)
		return 0;

	tat.msg.pid = getpid();
	tat.msg.tid = tid;

	return debug_send_packet(debug_fd, &(tat.hdr));
}

/* d9s_tresume resumes execution in all threads.
 *
 * This looks a bit different than all the other routines: The actual op is done
 * after sending a successful response. The response basically serves to let the
 * client know that the message was received, but not that the work was done.
 *
 * There's two scenarios for resume we care about at the moment:
 * 1) We resume and run until the program hits another breakpoint.
 * 2) We resume and run until the program exits.
 *
 * In the second case, the program could exit before the 2LS has a chance to
 * send the successful response. So we send the response first and assume that
 * resume cannot fail. (If it does, it wouldn't fail in a way we can currently
 * detect anyway.)
 */
static int d9s_tresume(struct d9_header *hdr, void *data)
{
	int ret;
	struct d9_rresume resp = D9_INIT_HDR(sizeof(struct d9_rresume), D9_RRESUME);
	struct d9_tresume *dtr = (struct d9_tresume *) hdr;

	if (d9_ops == NULL || d9_ops->resume == NULL)
		return debug_send_error(EBADF /* TODO: better error code */);

	ret = debug_send_packet(debug_fd, &(resp.hdr));

	/* Call user-supplied routine. */
	d9_ops->resume(dtr->msg.singlestep);

	return ret;
}

/* d9s_tstoremem allocates the response packet, calls the user-supplied ops
 * function for storing memory, and sends the response packet. */
static int d9s_tstoremem(struct d9_header *hdr, void *data)
{
	int ret;
	struct d9_rstoremem resp =
		D9_INIT_HDR(sizeof(struct d9_rstoremem), D9_RSTOREMEM);
	struct d9_tstoremem_msg *tstoremem = (struct d9_tstoremem_msg *) data;

	if (d9_ops == NULL || d9_ops->store_memory == NULL)
		return debug_send_error(EBADF /* TODO: better error code */);

	/* Call user-supplied routine for filling in response packet. */
	ret = d9_ops->store_memory(tstoremem);

	if (ret < 0)
		return debug_send_error(-ret);

	return debug_send_packet(debug_fd, &(resp.hdr));
}

/* d9s_treadmem allocates the response packet, calls the user-supplied ops
 * function for reading from memory, and sends the response packet. */
static int d9s_treadmem(struct d9_header *hdr, void *data)
{
	int ret;
	struct d9_rreadmem *resp;
	struct d9_treadmem_msg *treadmem = (struct d9_treadmem_msg *) data;
	struct d9_header *rhdr =
		alloc_packet(sizeof(struct d9_rreadmem) + treadmem->length,
					 D9_RREADMEM);
	if (rhdr == NULL)
		return debug_send_error(ENOMEM /* TODO */);

	if (d9_ops == NULL || d9_ops->read_memory == NULL)
		return debug_send_error(EBADF /* TODO */);

	resp = (struct d9_rreadmem *) rhdr;

	/* Call user-supplied routine for filling in response packet. */
	ret = d9_ops->read_memory(treadmem, &(resp->msg));

	if (ret < 0) {
		free(rhdr);
		return debug_send_error(-ret);
	}

	ret = debug_send_packet(debug_fd, rhdr);
	free(rhdr);
	return ret;
}

/* d9s_tstorereg allocates the response packet, finds the appropriate thread
 * structure, calls the user-supplied ops function for storing its registers,
 * and sends the response packet. */
static int d9s_tstorereg(struct d9_header *hdr, void *data)
{
	int ret;
	struct uthread *t;
	struct d9_header *rpack;
	struct d9_rstorereg resp =
		D9_INIT_HDR(sizeof(struct d9_rstorereg), D9_RSTOREREG);
	struct d9_tstorereg_msg *req = (struct d9_tstorereg_msg *) data;

	if (d9_ops == NULL || d9_ops->store_registers == NULL)
		return debug_send_error(EBADF /* TODO */);

	/* Find the appropriate thread. */
	t = uthread_get_thread_by_id(req->threadid);
	if (t == NULL)
		return debug_send_error(EBADF /* TODO */);

	/* Call user-supplied routine for filling in response packet. */
	ret = d9_ops->store_registers(t, &(req->regs));

	if (ret < 0)
		return debug_send_error(-ret);

	/* Successful response. */
	return debug_send_packet(debug_fd, &(resp.hdr));
}

/* d9s_tfetchreg allocates the response packet, finds the appropriate thread
 * structure, calls the user-supplied ops function for reading its registers,
 * and sends the response packet. */
static int d9s_tfetchreg(struct d9_header *hdr, void *data)
{
	int ret;
	struct uthread *t;
	struct d9_rfetchreg resp =
		D9_INIT_HDR(sizeof(struct d9_rfetchreg), D9_RFETCHREG);
	struct d9_tfetchreg_msg *req = (struct d9_tfetchreg_msg *) data;

	if (d9_ops == NULL || d9_ops->fetch_registers == NULL)
		return debug_send_error(EBADF /* TODO */);

	/* Find the appropriate thread. */
	t = uthread_get_thread_by_id(req->threadid);
	if (t == NULL)
		return debug_send_error(EBADF /* TODO */);

	/* Call user-supplied routine for filling in response packet. */
	ret = d9_ops->fetch_registers(t, &(resp.msg.regs));

	if (ret < 0)
		return debug_send_error(-ret);

	return debug_send_packet(debug_fd, &(resp.hdr));
}

/* debug_send_error sends an error response to gdbserver. */
static int debug_send_error(uint32_t errnum)
{
	struct d9_rerror rerror = D9_INIT_HDR(sizeof(struct d9_rerror), D9_RERROR);

	rerror.msg.errnum = errnum;

	return debug_send_packet(debug_fd, &(rerror.hdr));
}

static int debug_send_packet(int fd, struct d9_header *hdr)
{
	ssize_t wlen, total = 0;

	while (total < hdr->size) {
		wlen = write(fd, (uint8_t *) hdr + total, hdr->size - total);
		if (wlen < 0) {
			if (errno == EINTR)
				continue;
			else
				return -1;
		}
		total += wlen;
	}
	return 0;
}

/* read_all will keep calling read until `size` bytes have been read or an error
 * occurs. */
static int read_all(int fd, void *data, size_t size)
{
	ssize_t rlen, len_read = 0;

	while (len_read < size) {
		rlen = read(fd, (uint8_t *) data + len_read, size - len_read);
		if (rlen < 0) {
			if (errno == EINTR)
				continue;
			else
				return -1;
		}
		len_read += rlen;
	}
	return 0;
}

/* debug_read_packet will read a packet in its exact length. */
static struct d9_header *debug_read_packet(int fd)
{
	size_t msg_size;
	struct d9_header *hdr = malloc(sizeof(struct d9_header));

	if (hdr == NULL)
		panic("2LS debug: could not malloc");

	/* Read message header. */
	if (read_all(fd, hdr, sizeof(struct d9_header))) {
		free(hdr);
		return NULL;
	}

	/* Read the remaining bytes of the message. */
	msg_size = hdr->size - sizeof(struct d9_header);
	if (msg_size > 0) {
		hdr = realloc(hdr, hdr->size);
		if (hdr == NULL)
			panic("2LS debug: could not realloc");

		if (read_all(fd, hdr + 1, msg_size)) {
			perror("d9 read");
			free(hdr);
			return NULL;
		}
	}

	return hdr;
}

/* Globals to deal with incoming messages on gdbserver side.
 *
 * TODO(chrisko): Instead of making these global, make a struct to pass to
 * read_thread and the d9c_ functions.
 */
static struct d9_header *d9c_message;
static uth_mutex_t sync_lock;
static uth_cond_var_t sync_cv;

void *d9c_read_thread(void *arg)
{
	struct d9_header *hdr;
	int fd = *((int *) arg);
	ssize_t rlen = 0;

	while (1) {
		hdr = debug_read_packet(fd);
		if (hdr == NULL)
			return NULL;

		if (IS_MSG_R(hdr->msg_type)) {
			/* If this is a response message type, the main gdbserver thread is
			 * blocked on this response. */
			uth_mutex_lock(sync_lock);
			d9c_message = hdr;
			uth_mutex_unlock(sync_lock);
			uth_cond_var_broadcast(sync_cv);
		} else if (clt_msg_handlers[D9_HANDLER(hdr->msg_type)]) {
			/* This is a message that isn't a response to a request (e.g. a
			 * thread was added or we hit a breakpoint). */
			clt_msg_handlers[D9_HANDLER(hdr->msg_type)](hdr);
			free(hdr);
		} else {
			panic("2LS received invalid message type (type = %d, size = %d)\n",
			      hdr->msg_type, hdr->size);
			free(hdr);
		}
	}
}

static struct d9c_ops *client_ops;

/* d9c_thitbreakpoint is called when the 2LS sends a THITBREAKPOINT msg. */
int d9c_thitbreakpoint(struct d9_header *hdr)
{
	struct d9_thitbreakpoint *thb = (struct d9_thitbreakpoint *) hdr;

	return client_ops->hit_breakpoint(thb->msg.pid, thb->msg.tid,
	                                  thb->msg.address);
}

/* d9c_taddthread is called when the 2LS sends a TADDTHREAD msg. */
int d9c_taddthread(struct d9_header *hdr)
{
	struct d9_taddthread *tat = (struct d9_taddthread *) hdr;

	return client_ops->add_thread(tat->msg.pid, tat->msg.tid);
}

void d9c_init(struct d9c_ops *ops)
{
	sync_lock = uth_mutex_alloc();
	sync_cv = uth_cond_var_alloc();
	client_ops = ops;
	clt_msg_handlers[D9_HANDLER(D9_THITBREAKPOINT)] = &d9c_thitbreakpoint;
	clt_msg_handlers[D9_HANDLER(D9_TADDTHREAD)] = &d9c_taddthread;
}

static int check_error_packet(struct d9_header *hdr, enum d9_msg_t expected)
{
	struct d9_rerror *rerror;

	/* Msg is of expected type -- no error. */
	if (hdr->msg_type == expected)
		return 0;

	if (hdr->msg_type == D9_RERROR) {
		/* Got error message. */
		rerror = (struct d9_rerror *) hdr;
		errno = rerror->msg.errnum;
	} else {
		/* Neither got an error message nor the expected message. */
		errno = EIO;
	}
	return 1;
}

/* d9c_store_memory communicates with the 2LS to store from an address in
 * memory. */
int d9c_store_memory(int fd, uintptr_t address, const void *const data,
                     uint32_t length)
{
	struct d9_header *hdr, *rhdr;
	struct d9_tstoremem *req;

	rhdr = alloc_packet(sizeof(struct d9_tstoremem) + length, D9_TSTOREMEM);
	if (rhdr == NULL)
		return -1;

	req = (struct d9_tstoremem *) rhdr;
	req->msg.address = address;
	req->msg.length = length;
	memcpy(&(req->msg.data), data, length);

	int ret = debug_send_packet(fd, rhdr);

	/* Wait for response message. */
	uth_mutex_lock(sync_lock);
	while (d9c_message == NULL)
		uth_cond_var_wait(sync_cv, sync_lock);

	/* Got response. */
	if (check_error_packet(d9c_message, D9_RSTOREMEM)) {
		perror("d9 store memory");
		ret = -1;
	} else {
		ret = 0;
	}

	free(d9c_message);
	d9c_message = NULL;
	uth_mutex_unlock(sync_lock);
	free(rhdr);
	return ret;
}

/* d9c_read_memory communicates with the 2LS to read from an address in memory.
*/
int d9c_read_memory(int fd, uintptr_t address, uint32_t length, uint8_t *buf)
{
	int ret;
	struct d9_treadmem req =
		D9_INIT_HDR(sizeof(struct d9_treadmem), D9_TREADMEM);
	struct d9_rreadmem *resp;

	req.msg.address = address;
	req.msg.length = length;

	ret = debug_send_packet(fd, &(req.hdr));
	if (ret)
		return ret;

	/* Wait for response message. */
	uth_mutex_lock(sync_lock);
	while (d9c_message == NULL)
		uth_cond_var_wait(sync_cv, sync_lock);

	if (check_error_packet(d9c_message, D9_RREADMEM)) {
		perror("d9 read memory");
		ret = -1;
	} else {
		resp = (struct d9_rreadmem *) d9c_message;
		memcpy(buf, resp->msg.data, length);
		ret = 0;
	}

	free(d9c_message);
	d9c_message = NULL;
	uth_mutex_unlock(sync_lock);
	return ret;
}

/* d9c_store_registers communicates with the 2LS to change register values. */
int d9c_store_registers(int fd, uint64_t tid, struct d9_regs *regs)
{
	int ret;
	struct d9_tstorereg req =
		D9_INIT_HDR(sizeof(struct d9_tstorereg), D9_TSTOREREG);

	req.msg.threadid = tid;
	memcpy(&(req.msg.regs), regs, sizeof(struct d9_regs));

	ret = debug_send_packet(fd, &(req.hdr));
	if (ret)
		return ret;

	/* Wait for response message. */
	uth_mutex_lock(sync_lock);
	while (d9c_message == NULL)
		uth_cond_var_wait(sync_cv, sync_lock);

	if (check_error_packet(d9c_message, D9_RSTOREREG)) {
		perror("d9 read memory");
		ret = -1;
	} else {
		ret = 0;
	}

	free(d9c_message);
	d9c_message = NULL;
	uth_mutex_unlock(sync_lock);
	return ret;
}

/* d9c_fetch_registers communicates with the 2LS to read register values. */
int d9c_fetch_registers(int fd, uint64_t tid, struct d9_regs *regs)
{
	int ret;
	struct d9_rfetchreg *resp;
	struct d9_tfetchreg req =
		D9_INIT_HDR(sizeof(struct d9_tfetchreg), D9_TFETCHREG);

	req.msg.threadid = tid;

	ret = debug_send_packet(fd, &(req.hdr));
	if (ret)
		return ret;

	/* Wait for response message. */
	uth_mutex_lock(sync_lock);
	while (d9c_message == NULL)
		uth_cond_var_wait(sync_cv, sync_lock);

	if (check_error_packet(d9c_message, D9_RFETCHREG)) {
		perror("d9 read memory");
		ret = -1;
	} else {
		resp = (struct d9_rfetchreg *) d9c_message;
		memcpy(regs, &(resp->msg.regs), sizeof(struct d9_regs));
		ret = 0;
	}

	free(d9c_message);
	d9c_message = NULL;
	uth_mutex_unlock(sync_lock);
	return ret;
}

/* d9c_resume tells the 2LS to resume all threads. */
int d9c_resume(int fd, bool singlestep)
{
	int ret;
	struct d9_tresume req = D9_INIT_HDR(sizeof(struct d9_tresume), D9_TRESUME);

	req.msg.singlestep = singlestep;

	ret = debug_send_packet(fd, &(req.hdr));
	if (ret)
		return ret;

	/* Wait for response message. */
	uth_mutex_lock(sync_lock);
	while (d9c_message == NULL)
		uth_cond_var_wait(sync_cv, sync_lock);

	if (check_error_packet(d9c_message, D9_RRESUME)) {
		perror("d9 read memory");
		ret = -1;
	} else {
		ret = 0;
	}

	free(d9c_message);
	d9c_message = NULL;
	uth_mutex_unlock(sync_lock);
	return ret;
}
