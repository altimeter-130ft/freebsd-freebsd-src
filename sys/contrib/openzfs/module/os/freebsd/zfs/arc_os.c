/*
 * CDDL HEADER START
 *
 * The contents of this file are subject to the terms of the
 * Common Development and Distribution License (the "License").
 * You may not use this file except in compliance with the License.
 *
 * You can obtain a copy of the license at usr/src/OPENSOLARIS.LICENSE
 * or http://www.opensolaris.org/os/licensing.
 * See the License for the specific language governing permissions
 * and limitations under the License.
 *
 * When distributing Covered Code, include this CDDL HEADER in each
 * file and include the License file at usr/src/OPENSOLARIS.LICENSE.
 * If applicable, add the following below this CDDL HEADER, with the
 * fields enclosed by brackets "[]" replaced with your own identifying
 * information: Portions Copyright [yyyy] [name of copyright owner]
 *
 * CDDL HEADER END
 */

#include <sys/spa.h>
#include <sys/zio.h>
#include <sys/spa_impl.h>
#include <sys/counter.h>
#include <sys/zio_compress.h>
#include <sys/zio_checksum.h>
#include <sys/zfs_context.h>
#include <sys/arc.h>
#include <sys/zfs_refcount.h>
#include <sys/vdev.h>
#include <sys/vdev_trim.h>
#include <sys/vdev_impl.h>
#include <sys/dsl_pool.h>
#include <sys/zio_checksum.h>
#include <sys/multilist.h>
#include <sys/abd.h>
#include <sys/zil.h>
#include <sys/fm/fs/zfs.h>
#include <sys/eventhandler.h>
#include <sys/callb.h>
#include <sys/kstat.h>
#include <sys/zthr.h>
#include <zfs_fletcher.h>
#include <sys/arc_impl.h>
#include <sys/sdt.h>
#include <sys/aggsum.h>
#include <sys/vnode.h>
#include <cityhash.h>
#include <machine/vmparam.h>
#include <sys/vm.h>
#include <sys/vmmeter.h>
#include <sys/zfs_vfsops_os.h>
#include <vm/vm_pageout.h>

#if __FreeBSD_version >= 1300139
static struct sx arc_vnlru_lock;
static struct vnode *arc_vnlru_marker;
#endif

extern struct vfsops zfs_vfsops;

uint_t zfs_arc_free_target = 0;

static void
arc_free_target_init(void *unused __unused)
{
	zfs_arc_free_target = vm_cnt.v_free_target;
}
SYSINIT(arc_free_target_init, SI_SUB_KTHREAD_PAGE, SI_ORDER_ANY,
    arc_free_target_init, NULL);

/*
 * We don't have a tunable for arc_free_target due to the dependency on
 * pagedaemon initialisation.
 */
static int
sysctl_vfs_zfs_arc_free_target(SYSCTL_HANDLER_ARGS)
{
	uint_t val;
	int err;

	val = zfs_arc_free_target;
	err = sysctl_handle_int(oidp, &val, 0, req);
	if (err != 0 || req->newptr == NULL)
		return (err);

	if (val < minfree)
		return (EINVAL);
	if (val > vm_cnt.v_page_count)
		return (EINVAL);

	zfs_arc_free_target = val;

	return (0);
}
SYSCTL_DECL(_vfs_zfs);
/* BEGIN CSTYLED */
SYSCTL_PROC(_vfs_zfs, OID_AUTO, arc_free_target,
    CTLTYPE_UINT | CTLFLAG_MPSAFE | CTLFLAG_RW, 0, sizeof (uint_t),
    sysctl_vfs_zfs_arc_free_target, "IU",
    "Desired number of free pages below which ARC triggers reclaim");
/* END CSTYLED */

int64_t
arc_available_memory(void)
{
	int64_t lowest = INT64_MAX;
	int64_t n __unused;

	/*
	 * Cooperate with pagedaemon when it's time for it to scan
	 * and reclaim some pages.
	 */
	n = PAGESIZE * ((int64_t)freemem - zfs_arc_free_target);
	if (n < lowest) {
		lowest = n;
	}
#if defined(__i386) || !defined(UMA_MD_SMALL_ALLOC)
	/*
	 * If we're on an i386 platform, it's possible that we'll exhaust the
	 * kernel heap space before we ever run out of available physical
	 * memory.  Most checks of the size of the heap_area compare against
	 * tune.t_minarmem, which is the minimum available real memory that we
	 * can have in the system.  However, this is generally fixed at 25 pages
	 * which is so low that it's useless.  In this comparison, we seek to
	 * calculate the total heap-size, and reclaim if more than 3/4ths of the
	 * heap is allocated.  (Or, in the calculation, if less than 1/4th is
	 * free)
	 */
	n = uma_avail() - (long)(uma_limit() / 4);
	if (n < lowest) {
		lowest = n;
	}
#endif

	DTRACE_PROBE1(arc__available_memory, int64_t, lowest);
	return (lowest);
}

/*
 * Return a default max arc size based on the amount of physical memory.
 */
uint64_t
arc_default_max(uint64_t min, uint64_t allmem)
{
	uint64_t size;

	if (allmem >= 1 << 30)
		size = allmem - (1 << 30);
	else
		size = min;
	return (MAX(allmem * 5 / 8, size));
}

/* The flag indicating a running ARC pruning task. */
static int arc_prune_running;

/*
 * Helper function for arc_prune_async() it is responsible for safely
 * handling the execution of a registered arc_prune_func_t.
 */
static void
arc_prune_task(void *arg)
{
	boolean_t update_ts_last_withwaiter;
	int64_t zn_prunable, dn_total, zn_to_scan, dn_to_scan, zn_delta;
	uint64_t zn_total, zn_inuse;
	struct timespec ts_now, ts_delta;
	static struct timespec ts_last_withwaiter;
	static const struct timespec ts_pause_withwaiter =
	    {.tv_sec = 1, .tv_nsec = 0};

	dn_to_scan = (intptr_t)arg;

	wmsum_add(&zfs_znode_pruning_requested, 1);

	zn_total = atomic_load_acq_64(&zfs_znode_count);
	zn_inuse = atomic_load_acq_64(&zfs_znode_inuse_count);

	/*
	 * Work around the in-use counter error that may happen under a heavy load.
	 *
	 * Fix the in-use counter value only when the counters are stable, ie their
	 * values do not change across multiple reads.  Otherwise, defer the fix to
	 * the next chance.
	 */
	if (__predict_false(zn_total < zn_inuse))
		zn_delta = zn_inuse - zn_total;
	else if (__predict_false(((int64_t)zn_inuse) < 0))
		zn_delta = (int64_t)zn_inuse;
	else
		zn_delta = 0;

	if (__predict_false(0 != zn_delta)) {
		if (zn_total == atomic_load_64(&zfs_znode_count)) {
			if (atomic_cmpset_64(&zfs_znode_inuse_count,
			    zn_inuse,
			    zn_inuse - zn_delta)) {
				if (__predict_false(
				    zn_total != atomic_load_64(&zfs_znode_count))) {
					atomic_add_64(&zfs_znode_inuse_count, zn_delta);
				}
			}
		}
	}

	zn_prunable = zn_total - zn_inuse - zn_delta;

	/*
	 * Scale the number of the prunable dnodes into the znodes by the total
	 * number of the znodes and dnodes.  A znode may span across multiple
	 * dnodes, but the precise span estimation is both complicated and opaque
	 * to the znode and vnode sides.
	 *
	 * Assume that the numbers of the znodes and dnodes fit within the 32 bit
	 * integer type.
	 */
	zn_to_scan = dn_to_scan * zn_total;
	dn_total = aggsum_value(&arc_sums.arcstat_dnode_size) / sizeof(dnode_t);
	zn_to_scan /= dn_total;

	update_ts_last_withwaiter = B_FALSE;

	if (arc_is_waiting_evict()) {
		/*
		 * Someone wants the ARC eviction.  Prune everything unless there are
		 * no prunable vnodes at all.
		 *
		 * Limit the rate up to 1 [Hz] because this eviction makes the vnode
		 * allocation so expensive.
		 */
		wmsum_add(&zfs_znode_pruning_withwaiter, 1);
		getnanotime(&ts_now);
		timespecsub(&ts_now, &ts_last_withwaiter, &ts_delta);
		if (timespeccmp(&ts_delta, &ts_pause_withwaiter, >=)) {
			if (zn_prunable < zn_to_scan)
				zn_to_scan = zn_prunable;
			update_ts_last_withwaiter = B_TRUE;
		} else
			wmsum_add(&zfs_znode_pruning_withwaiter_throttled, 1);
	}
	if ((zn_prunable < zn_to_scan) || (0 == zn_to_scan)) {
		wmsum_add(&zfs_znode_pruning_skipped, 1);
		goto done;
	}

	arc_reduce_target_size(ptob(zn_to_scan));

#ifndef __ILP32__
	if (zn_to_scan > INT_MAX)
		zn_to_scan = INT_MAX;
#endif

	if (zn_to_scan > 0) {
#if __FreeBSD_version >= 1300139
		sx_xlock(&arc_vnlru_lock);
		vnlru_free_vfsops(zn_to_scan, &zfs_vfsops, arc_vnlru_marker);
		sx_xunlock(&arc_vnlru_lock);
#else
		vnlru_free(zn_to_scan, &zfs_vfsops);
#endif
	}

	if (update_ts_last_withwaiter)
		getnanotime(&ts_last_withwaiter);

done:
	atomic_store_rel_int(&arc_prune_running, 0);
}

/*
 * Notify registered consumers they must drop holds on a portion of the ARC
 * buffered they reference.  This provides a mechanism to ensure the ARC can
 * honor the arc_meta_limit and reclaim otherwise pinned ARC buffers.  This
 * is analogous to dnlc_reduce_cache() but more generic.
 *
 * This operation is performed asynchronously so it may be safely called
 * in the context of the arc_reclaim_thread().  A reference is taken here
 * for each registered arc_prune_t and the arc_prune_task() is responsible
 * for releasing it once the registered arc_prune_func_t has completed.
 */
void
arc_prune_async(int64_t adjust)
{
	int ret;

	/* Avoid piling up the ARC pruning tasks. */
	ret = atomic_cmpset_acq_int(&arc_prune_running, 0, 1);
	if (!ret)
		return;

#ifndef __LP64__
	if (adjust > INTPTR_MAX)
		adjust = INTPTR_MAX;
#endif
	taskq_dispatch(arc_prune_taskq, arc_prune_task,
	    (void *)(intptr_t)adjust, TQ_SLEEP);
	ARCSTAT_BUMP(arcstat_prune);
}

uint64_t
arc_all_memory(void)
{
	return (ptob(physmem));
}

int
arc_memory_throttle(spa_t *spa, uint64_t reserve, uint64_t txg)
{
	return (0);
}

uint64_t
arc_free_memory(void)
{
	return (ptob(freemem));
}

static eventhandler_tag arc_event_lowmem = NULL;

/*
 * The vm_lowmem event counters.
 */
wmsum_t zfs_arc_vm_lowmem_events;
wmsum_t zfs_arc_vm_lowmem_kmem;
wmsum_t zfs_arc_vm_lowmem_pages;
wmsum_t zfs_arc_vm_lowmem_nofree;
wmsum_t zfs_arc_vm_lowmem_pagedaemon;

static void
arc_lowmem(void *arg __unused, int howto)
{
	int64_t free_memory, to_free;

	wmsum_add(&zfs_arc_vm_lowmem_events, 1);
	switch (howto) {
	case VM_LOW_KMEM:
		wmsum_add(&zfs_arc_vm_lowmem_kmem, 1);
		break;

	case VM_LOW_PAGES:
		wmsum_add(&zfs_arc_vm_lowmem_pages, 1);
		break;

	default:
		break;
	}
	if (curproc == pageproc)
		wmsum_add(&zfs_arc_vm_lowmem_pagedaemon, 1);

	arc_no_grow = B_TRUE;
	arc_warm = B_TRUE;
	arc_growtime = gethrtime() + SEC2NSEC(arc_grow_retry);
	free_memory = arc_available_memory();
	int64_t can_free = arc_c - arc_c_min;
	if (can_free <= 0) {
		wmsum_add(&zfs_arc_vm_lowmem_nofree, 1);
		return;
	}
	to_free = (can_free >> arc_shrink_shift) - MIN(free_memory, 0);
	DTRACE_PROBE2(arc__needfree, int64_t, free_memory, int64_t, to_free);
	arc_reduce_target_size(to_free);

	/*
	 * It is unsafe to block here in arbitrary threads, because we can come
	 * here from ARC itself and may hold ARC locks and thus risk a deadlock
	 * with ARC reclaim thread.
	 */
	if (curproc == pageproc)
		arc_wait_for_eviction(to_free, B_FALSE);
}

void
arc_lowmem_init(void)
{
	wmsum_init(&zfs_arc_vm_lowmem_events, 0);
	wmsum_init(&zfs_arc_vm_lowmem_kmem, 0);
	wmsum_init(&zfs_arc_vm_lowmem_pages, 0);
	wmsum_init(&zfs_arc_vm_lowmem_nofree, 0);
	wmsum_init(&zfs_arc_vm_lowmem_pagedaemon, 0);
	arc_event_lowmem = EVENTHANDLER_REGISTER(vm_lowmem, arc_lowmem, NULL,
	    EVENTHANDLER_PRI_FIRST);
#if __FreeBSD_version >= 1300139
	arc_vnlru_marker = vnlru_alloc_marker();
	sx_init(&arc_vnlru_lock, "arc vnlru lock");
#endif
}

void
arc_lowmem_fini(void)
{
	if (arc_event_lowmem != NULL)
		EVENTHANDLER_DEREGISTER(vm_lowmem, arc_event_lowmem);
#if __FreeBSD_version >= 1300139
	if (arc_vnlru_marker != NULL) {
		vnlru_free_marker(arc_vnlru_marker);
		sx_destroy(&arc_vnlru_lock);
	}
#endif
	wmsum_fini(&zfs_arc_vm_lowmem_events);
	wmsum_fini(&zfs_arc_vm_lowmem_kmem);
	wmsum_fini(&zfs_arc_vm_lowmem_pages);
	wmsum_fini(&zfs_arc_vm_lowmem_nofree);
	wmsum_fini(&zfs_arc_vm_lowmem_pagedaemon);
}

void
arc_register_hotplug(void)
{
}

void
arc_unregister_hotplug(void)
{
}
