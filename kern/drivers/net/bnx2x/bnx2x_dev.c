/* This file is part of the UCB release of Plan 9. It is subject to the license
 * terms in the LICENSE file found in the top-level directory of this
 * distribution and at http://akaros.cs.berkeley.edu/files/Plan9License. No
 * part of the UCB release of Plan 9, including this file, may be copied,
 * modified, propagated, or distributed except according to the terms contained
 * in the LICENSE file. */

/* Network driver stub for bnx2x_ */

#include <vfs.h>
#include <kfs.h>
#include <slab.h>
#include <kmalloc.h>
#include <kref.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>
#include <error.h>
#include <cpio.h>
#include <pmap.h>
#include <smp.h>
#include <arch/pci.h>
#include <ip.h>
#include <ns.h>
#include "bnx2x.h"

/* TODO: Cheap externs */
extern int __init bnx2x_init(void);
extern bool is_bnx2x_dev(struct pci_device *dev);
extern const struct pci_device_id *
                    srch_bnx2x_pci_tbl(struct pci_device *needle);
extern int bnx2x_init_one(struct ether *dev, struct bnx2x *bp,
                          struct pci_device *pdev,
                          const struct pci_device_id *ent);
extern int bnx2x_open(struct ether *dev);

spinlock_t bnx2x_tq_lock = SPINLOCK_INITIALIZER;
TAILQ_HEAD(bnx2x_tq, bnx2x);
struct bnx2x_tq bnx2x_tq = TAILQ_HEAD_INITIALIZER(bnx2x_tq);

/* We're required to print out stats at some point.  Here are a couple from
 * igbe, as an example. */
static char *statistics[Nstatistics] = {
	"CRC Error",
	"Alignment Error",
};

static long bnx2x_ifstat(struct ether *edev, void *a, long n, uint32_t offset)
{
	struct bnx2x *ctlr;
	char *p, *s;
	int i, l, r;
	uint64_t tuvl, ruvl;

	ctlr = edev->ctlr;
	qlock(&ctlr->slock);
	p = kzmalloc(READSTR, 0);
	if (p == NULL) {
		qunlock(&ctlr->slock);
		error(Enomem);
	}
	l = 0;
	for (i = 0; i < Nstatistics; i++) {
		/* somehow read the device's HW stats */
		//r = csr32r(ctlr, Statistics + i * 4);
		r = 3;	/* TODO: this is the value for the statistic */
		if ((s = statistics[i]) == NULL)
			continue;
		/* based on the stat, spit out a string */
		switch (i) {
			default:
				ctlr->statistics[i] += r;
				if (ctlr->statistics[i] == 0)
					continue;
				l += snprintf(p + l, READSTR - l, "%s: %ud %ud\n",
							  s, ctlr->statistics[i], r);
				break;
		}
	}

	/* TODO: then print out the software-only (ctlr) stats */
//	l += snprintf(p + l, READSTR - l, "lintr: %ud %ud\n",
//				  ctlr->lintr, ctlr->lsleep);
	n = readstr(offset, a, n, p);
	kfree(p);
	qunlock(&ctlr->slock);

	return n;
}

static long bnx2x_ctl(struct ether *edev, void *buf, long n)
{
	ERRSTACK(1);
	int v;
	char *p;
	struct bnx2x *ctlr;
	struct cmdbuf *cb;
	struct cmdtab *ct;

	if ((ctlr = edev->ctlr) == NULL)
		error(Enonexist);
	cb = parsecmd(buf, n);
	if (waserror()) {
		kfree(cb);
		nexterror();
	}

	/* TODO: handle ctl command somehow.  igbe did the following: */
	//ct = lookupcmd(cb, igbectlmsg, ARRAY_SIZE(igbectlmsg));
	
	kfree(cb);
	poperror();
	return n;
}

static void bnx2x_promiscuous(void *arg, int on)
{
	int rctl;
	struct bnx2x *ctlr;
	struct ether *edev;

	edev = arg;
	ctlr = edev->ctlr;
	/* TODO: set promisc on/off */
}

static void bnx2x_multicast(void *arg, uint8_t * addr, int add)
{
	int bit, x;
	struct bnx2x *ctlr;
	struct ether *edev;

	edev = arg;
	ctlr = edev->ctlr;
	/* TODO: add or remove a multicast addr */
}

/* Transmit initialization.  Not mandatory for 9ns, but a good idea */
static void bnx2x_txinit(struct bnx2x *ctlr)
{
}

static void bnx2x_transmit(struct ether *edev)
{
	struct block *bp;
	struct bnx2x *ctlr;

	ctlr = edev->ctlr;

	/* Don't forget to spin_lock_irqsave */

	/* TODO: Free any completed packets */

	/* Try to fill the ring back up.  While there is space, yank from the output
	 * queue (oq) and put them in the Tx desc. */
	while (1) {
	//while (NEXT_RING(tdt, ctlr->ntd) != tdh) {
		if ((bp = qget(edev->oq)) == NULL)
			break;
		//td = &ctlr->tdba[tdt];
		//td->addr[0] = paddr_low32(bp->rp);
		//td->addr[1] = paddr_high32(bp->rp);
		/* if we're breaking out, make sure to set the IRQ mask */
		//if (NEXT_RING(tdt, ctlr->ntd) == tdh) {
		//	// other stuff removed
		//	csr32w(ctlr, Tdt, tdt);
		//	igbeim(ctlr, Txdw);
		//	break;
		//}
	}
}

/* Not mandatory.  Called to make sure there are free blocks available for
 * incoming packets */
static void bnx2x_replenish(struct bnx2x *ctlr)
{
	struct block *bp;

	while (1) {
	//while (NEXT_RING(rdt, ctlr->nrd) != ctlr->rdh) {
		//if we want a new block
		{
			bp = iallocb(64); // TODO: use your block size, e.g. Rbsz
			if (bp == NULL) {
				/* needs to be a safe print for interrupt level */
				printk("#l%d bnx2x_replenish: no available buffers\n",
					   ctlr->edev->ctlrno);
				break;
			}
			//ctlr->rb[rdt] = bp;
			//rd->addr[0] = paddr_low32(bp->rp);
			//rd->addr[1] = paddr_high32(bp->rp);
		}
		wmb();	/* ensure prev rd writes come before status = 0. */
		//rd->status = 0;
	}
}

/* Not mandatory.  Device init. */
static void bnx2x_rxinit(struct bnx2x *ctlr)
{
	bnx2x_replenish(ctlr);
}

static int bnx2x_rim(void* ctlr)
{
	//return ((struct bnx2x*)ctlr)->rim != 0;
	return 1;
}

/* Do we want a receive proc?  It is similar to softirq.  Or we can do the work
 * in hard IRQ ctx. */
static void bnx2x_rproc(void *arg)
{
	struct block *bp;
	struct bnx2x *ctlr;
	struct ether *edev;

	edev = arg;
	ctlr = edev->ctlr;

	bnx2x_rxinit(ctlr);
	/* TODO: one time RX init */


	for (;;) {
		/* TODO: set up, once per sleep.  make sure we'll wake up */
		rendez_sleep(&ctlr->rrendez, bnx2x_rim, ctlr);

		for (;;) {
			/* if we can get a block, here's how to ram it up the stack */

			if (1) {
				bp = (void*)0xdeadbeef;
				//bp = ctlr->rb[rdh];
				//bp->wp += rd->length;
				//bp->next = NULL;
				/* conditionally, set block flags */
					//bp->flag |= Bipck; /* IP checksum done in HW */
					//bp->flag |= Btcpck | Budpck;
					//bp->checksum = rd->checksum;
					//bp->flag |= Bpktck;	/* Packet checksum? */
				etheriq(edev, bp, 1);
			} else {
				//freeb(ctlr->rb[rdh]);
			}

		}
		// optionally
			bnx2x_replenish(ctlr);
	}
}

static void bnx2x_attach(struct ether *edev)
{
	ERRSTACK(1);
	struct block *bp;
	struct bnx2x *ctlr;
	char *name;

	ctlr = edev->ctlr;
	ctlr->edev = edev;	/* point back to Ether* */

	/* not sure if we'll need/want any of the 9ns stuff */
	return;

	qlock(&ctlr->alock);
	/* TODO: make sure we haven't attached already.  If so, just return */

	/* Alloc all your ctrl crap. */

	/* the ktasks should free these names, if they ever exit */
	name = kmalloc(KNAMELEN, KMALLOC_WAIT);
	snprintf(name, KNAMELEN, "#l%d-bnx2x_rproc", edev->ctlrno);
	ktask(name, bnx2x_rproc, edev);

	bnx2x_txinit(ctlr);

	qunlock(&ctlr->alock);
}

/* Hard IRQ */
static void bnx2x_interrupt(struct hw_trapframe *hw_tf, void *arg)
{
	struct bnx2x *ctlr;
	struct ether *edev;
	int icr, im, txdw;

	edev = arg;
	ctlr = edev->ctlr;

			/* At some point, wake up the rproc */
			rendez_wakeup(&ctlr->rrendez);

	/* optionally, might need to transmit (not sure if this is a good idea in
	 * hard irq or not) */
	bnx2x_transmit(edev);
}

static void bnx2x_shutdown(struct ether *ether)
{
	/*
	 * Perform a device reset to get the chip back to the
	 * power-on state, followed by an EEPROM reset to read
	 * the defaults for some internal registers.
	 */
	/* igbe did: */
	//igbedetach(ether->ctlr);
}

/* "reset", getting it back to the basic power-on state.  9ns drivers call this
 * during the initial setup (from the PCI func) */
static int bnx2x_reset(struct bnx2x *ctlr)
{
	int ctrl, i, pause, r, swdpio, txcw;

	bnx2x_init_one(ctlr->edev, ctlr, ctlr->pcidev, ctlr->pci_id);
	bnx2x_open(ctlr->edev);
	/* despite the name, we attach at reset time.  BXE attach has a lot of
	 * mmio mappings that have to happen at boot (in akaros), instead of during
	 * devether's attach (at runtime) */

	/* shut it up for now.  too much stats output */
	ctlr->msg_enable = 0;

//extern int bnx2x_attach(struct bnx2x *sc);
//	bnx2x_attach(ctlr);
//
//	/* normally done during BSD's ifconfig */
//extern void bnx2x_init(void *xsc);
//	bnx2x_init(ctlr);

//	if (igbedetach(ctlr))
//		return -1;

	return 0;
}

static void bnx2x_pci(void)
{
	int cls, id;
	struct pci_device *pcidev;
	struct bnx2x *ctlr;
	const struct pci_device_id *pci_id;

	bnx2x_init();

	STAILQ_FOREACH(pcidev, &pci_devices, all_dev) {
		/* This checks that pcidev is a Network Controller for Ethernet */
		if (pcidev->class != 0x02 || pcidev->subclass != 0x00)
			continue;
		id = pcidev->dev_id << 16 | pcidev->ven_id;

		pci_id = srch_bnx2x_pci_tbl(pcidev);
		if (!pci_id)
			continue;

		printk("bnx2x driver found 0x%04x:%04x at %02x:%02x.%x\n",
			   pcidev->ven_id, pcidev->dev_id,
			   pcidev->bus, pcidev->dev, pcidev->func);

		/* MMIO, pci_bus_master, etc, are all done in bnx2x_attach */

		cls = pcidev_read8(pcidev, PCI_CLSZ_REG);
		switch (cls) {
			default:
				printd("bnx2x: unexpected CLS - %d\n", cls * 4);
				break;
			case 0x00:
			case 0xFF:
				/* bogus value; use a sane default.  cls is set in DWORD (u32)
				 * units. */
				cls = ARCH_CL_SIZE / sizeof(long);
				pcidev_write8(pcidev, PCI_CLSZ_REG, cls);
				break;
			case 0x08:
			case 0x10:
				break;
		}

		ctlr = kzmalloc(sizeof(struct bnx2x), 0);
		if (ctlr == NULL)
			error(Enomem);

		spinlock_init_irqsave(&ctlr->imlock);
		spinlock_init_irqsave(&ctlr->tlock);
		qlock_init(&ctlr->alock);
		qlock_init(&ctlr->slock);
		rendez_init(&ctlr->rrendez);

		ctlr->pcidev = pcidev;
		ctlr->pci_id = pci_id;
		
		spin_lock(&bnx2x_tq_lock);
		TAILQ_INSERT_TAIL(&bnx2x_tq, ctlr, link9ns);
		spin_unlock(&bnx2x_tq_lock);
	}
}

/* Called by devether's probe routines.  Return -1 if the edev does not match
 * any of your ctlrs. */
static int bnx2x_pnp(struct ether *edev)
{
	struct bnx2x *ctlr;

	/* Allocs ctlrs for all PCI devices matching our IDs, does various PCI and
	 * MMIO/port setup */
	run_once(bnx2x_pci());

	spin_lock(&bnx2x_tq_lock);
	TAILQ_FOREACH(ctlr, &bnx2x_tq, link9ns) {
		/* just take the first inactive ctlr on the list */
		if (ctlr->active)
			continue;
		ctlr->active = 1;
		break;
	}
	spin_unlock(&bnx2x_tq_lock);
	if (ctlr == NULL)
		return -1;

	edev->ctlr = ctlr;
	ctlr->edev = edev;

	//edev->port = ctlr->port;	/* might just remove this from devether */
	edev->irq = ctlr->pcidev->irqline;
	edev->tbdf = MKBUS(BusPCI, ctlr->pcidev->bus, ctlr->pcidev->dev,
	                   ctlr->pcidev->func);
	edev->mbps = 1000;
	memmove(edev->ea, ctlr->link_params.mac_addr, Eaddrlen);
	
	/*
	 * Linkage to the generic ethernet driver.
	 */
	edev->attach = bnx2x_attach;
	edev->transmit = bnx2x_transmit;
	edev->ifstat = bnx2x_ifstat;
	edev->ctl = bnx2x_ctl;
	edev->shutdown = bnx2x_shutdown;

	edev->arg = edev;
	edev->promiscuous = bnx2x_promiscuous;
	edev->multicast = bnx2x_multicast;

	/* Plan 9's MTU includes the header (e.g. 1514, instead of 1500).  Linux
	 * drivers expect just the payload and not the header, and will add in the
	 * 14 whenever it is needed.
	 *
	 * There might be issues when plan 9 code accesses maxmtu, now that it's
	 * 1500 instead of 1514.  Keep a lookout for Etoobig in etherwrite.  What a
	 * mess. */
	edev->maxmtu -= ETHERHDRSIZE;

	bnx2x_reset(ctlr);

	return 0;
}

linker_func_3(etherbnx2x_link)
{
	addethercard("bnx2x", bnx2x_pnp);
}
