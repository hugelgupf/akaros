/* Copyright (c) 2013 The Regents of the University of California
 * Barret Rhoden <brho@cs.berkeley.edu>
 * Kevin Klues <klueska@cs.berkeley.edu>
 *
 * Spinlocks and Spin-PDR locks (preemption detection/recovery)
 *
 * See LICENSE for details. */

#pragma once

#include <parlib/arch/arch.h>
#include <parlib/arch/atomic.h>

__BEGIN_DECLS

#define SPINLOCK_INITIALIZER {0}

typedef struct {
  int lock;
} spinlock_t;

void spinlock_init(spinlock_t *lock);
int spinlock_trylock(spinlock_t *lock);
void spinlock_lock(spinlock_t *lock);
void spinlock_unlock(spinlock_t *lock);
bool spinlock_locked(spinlock_t *lock);

/* RISCV doesn't support CAS, so til it does, we use the NO_CAS, even if they
 * didn't ask for it in their config. */
#ifdef __riscv__
# ifndef CONFIG_SPINPDR_NO_CAS
#  define CONFIG_SPINPDR_NO_CAS 1
# endif
#endif

/* Two different versions, with and without CAS.  Default is with CAS. */
#ifndef CONFIG_SPINPDR_NO_CAS

# define SPINPDR_UNLOCKED ((uint32_t)-1)

struct spin_pdr_lock {
	uint32_t lock;
};
# define SPINPDR_INITIALIZER {SPINPDR_UNLOCKED}

#else /* NO_CAS */

# define SPINPDR_VCOREID_UNKNOWN ((uint32_t)-1)

struct spin_pdr_lock {
	/* consider putting these on separate cache lines, if we ever use them */
	spinlock_t spinlock;
	uint32_t lockholder;
};
# define SPINPDR_INITIALIZER {SPINLOCK_INITIALIZER, SPINPDR_VCOREID_UNKNOWN}

#endif /* CONFIG_SPINPDR_NO_CAS */

typedef struct spin_pdr_lock spinpdrlock_t;

void spin_pdr_init(struct spin_pdr_lock *pdr_lock);
void spin_pdr_lock(struct spin_pdr_lock *pdr_lock);
void spin_pdr_unlock(struct spin_pdr_lock *pdr_lock);
bool spin_pdr_locked(struct spin_pdr_lock *pdr_lock);

__END_DECLS
