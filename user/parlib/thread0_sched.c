/* Copyright (c) 2015 Google, Inc.
 * Barret Rhoden <brho@cs.berkeley.edu>
 * See LICENSE for details.
 *
 * thread0_sched: a basic scheduler for thread0, used by SCPs without a
 * multithreaded 2LS linked in.
 *
 * This is closely coupled with uthread.c */

#include <parlib/arch/atomic.h>
#include <parlib/arch/trap.h>
#include <parlib/debug.h>
#include <parlib/event.h>
#include <parlib/parlib.h>
#include <parlib/uthread.h>
#include <parlib/vcore.h>
#include <ros/arch/membar.h>
#include <stdlib.h>

static void thread0_sched_entry(void);
static void thread0_thread_blockon_sysc(struct uthread *uthread, void *sysc);
static void thread0_thread_refl_fault(struct uthread *uth,
                                      struct user_context *ctx);
static void thread0_thread_runnable(struct uthread *uth);
static void thread0_thread_has_blocked(struct uthread *uth, int flags);
static uth_mutex_t thread0_mtx_alloc(void);
static void thread0_mtx_free(uth_mutex_t m);
static void thread0_mtx_lock(uth_mutex_t m);
static void thread0_mtx_unlock(uth_mutex_t m);

/* externed into uthread.c */
struct schedule_ops thread0_2ls_ops = {
    .sched_entry = thread0_sched_entry,
    .thread_blockon_sysc = thread0_thread_blockon_sysc,
    .thread_refl_fault = thread0_thread_refl_fault,
    .thread_runnable = thread0_thread_runnable,
    .thread_paused = thread0_thread_runnable,
    .thread_has_blocked = thread0_thread_has_blocked,
    .mutex_alloc = thread0_mtx_alloc,
    .mutex_free = thread0_mtx_free,
    .mutex_lock = thread0_mtx_lock,
    .mutex_unlock = thread0_mtx_unlock,
};

static struct d9_ops thread0_d9ops = {
    .read_memory = &d9s_read_memory,
    .store_memory = &d9s_store_memory,
    .fetch_registers = &d9_fetch_registers,
};

/* externed into uthread.c */
struct uthread *thread0_uth;

/* Our thread0 is actually allocated in uthread as just a struct uthread, so we
 * don't actually attach this mgmt info to it.  But since we just have one
 * thread, it doesn't matter. */
struct thread0_info {
	bool is_blocked;
};
static struct thread0_info thread0_info;
static struct event_queue *sysc_evq;

static void thread0_handle_syscall(struct event_msg *ev_msg,
                                   unsigned int ev_type, void *data)
{
	thread0_info.is_blocked = FALSE;
}

void thread0_lib_init(void)
{
	memset(&thread0_info, 0, sizeof(thread0_info));
	/* we don't care about the message, so don't bother with a UCQ */
	sysc_evq = get_eventq(EV_MBOX_BITMAP);
	sysc_evq->ev_flags = EVENT_INDIR | EVENT_WAKEUP;
	register_ev_handler(EV_SYSCALL, thread0_handle_syscall, 0);

	/* Make ourselves available for debugging */
	d9s_init(&thread0_d9ops);
}

/* Thread0 scheduler ops (for processes that haven't linked in a full 2LS) */
static void thread0_sched_entry(void)
{
	/* TODO: support signal handling whenever we run a uthread */
	if (current_uthread) {
		uthread_prep_pending_signals(current_uthread);
		run_current_uthread();
		assert(0);
	}
	while (1) {
		if (!thread0_info.is_blocked) {
			uthread_prep_pending_signals(thread0_uth);
			run_uthread(thread0_uth);
			assert(0);
		}
		sys_yield(FALSE);
		handle_events(0);
	}
}

static void thread0_thread_blockon_sysc(struct uthread *uthread, void *arg)
{
	struct syscall *sysc = (struct syscall *)arg;
	thread0_thread_has_blocked(uthread, 0);
	if (!register_evq(sysc, sysc_evq))
		thread0_thread_runnable(uthread);
}

static void refl_error(struct uthread *uth, unsigned int trap_nr,
                       unsigned int err, unsigned long aux)
{
	printf("Thread has unhandled fault: %d, err: %d, aux: %p\n", trap_nr, err,
	       aux);
	/* Note that uthread.c already copied out our ctx into the uth
	 * struct */
	print_user_context(&uth->u_ctx);
	printf("Turn on printx to spew unhandled, malignant trap info\n");
	exit(-1);
}

static bool handle_page_fault(struct uthread *uth, unsigned int err,
                              unsigned long aux)
{
	if (!(err & PF_VMR_BACKED))
		return FALSE;
	syscall_async(&uth->local_sysc, SYS_populate_va, aux, 1);
	__block_uthread_on_async_sysc(uth);
	return TRUE;
}

static void thread0_thread_refl_fault(struct uthread *uth,
                                      struct user_context *ctx)
{
	unsigned int trap_nr = __arch_refl_get_nr(ctx);
	unsigned int err = __arch_refl_get_err(ctx);
	unsigned long aux = __arch_refl_get_aux(ctx);

	assert(ctx->type == ROS_HW_CTX);
	switch (trap_nr) {
	case HW_TRAP_PAGE_FAULT:
		if (!handle_page_fault(uth, err, aux))
			refl_error(uth, trap_nr, err, aux);
		break;
	default:
		refl_error(uth, trap_nr, err, aux);
	}
}

static void thread0_thread_runnable(struct uthread *uth)
{
	thread0_info.is_blocked = FALSE;
}

static void thread0_thread_has_blocked(struct uthread *uth, int flags)
{
	thread0_info.is_blocked = TRUE;
}

/* We only have one thread, so we don't need mutexes */
static uth_mutex_t thread0_mtx_alloc(void)
{
	/* Returning something non-zero, in case someone compares it to 0 */
	return (uth_mutex_t)0x1234;
}

static void thread0_mtx_free(uth_mutex_t m)
{
}

static void thread0_mtx_lock(uth_mutex_t m)
{
}

static void thread0_mtx_unlock(uth_mutex_t m)
{
}
