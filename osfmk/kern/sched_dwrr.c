/*
 * Copyright (c) 2009 Apple Inc. All rights reserved.
 *
 * @APPLE_OSREFERENCE_LICENSE_HEADER_START@
 *
 * This file contains Original Code and/or Modifications of Original Code
 * as defined in and that are subject to the Apple Public Source License
 * Version 2.0 (the 'License'). You may not use this file except in
 * compliance with the License. The rights granted to you under the License
 * may not be used to create, or enable the creation or redistribution of,
 * unlawful or unlicensed copies of an Apple operating system, or to
 * circumvent, violate, or enable the circumvention or violation of, any
 * terms of an Apple operating system software license agreement.
 *
 * Please obtain a copy of the License at
 * http://www.opensource.apple.com/apsl/ and read it before using this file.
 *
 * The Original Code and all software distributed under the License are
 * distributed on an 'AS IS' basis, WITHOUT WARRANTY OF ANY KIND, EITHER
 * EXPRESS OR IMPLIED, AND APPLE HEREBY DISCLAIMS ALL SUCH WARRANTIES,
 * INCLUDING WITHOUT LIMITATION, ANY WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE, QUIET ENJOYMENT OR NON-INFRINGEMENT.
 * Please see the License for the specific language governing rights and
 * limitations under the License.
 *
 * @APPLE_OSREFERENCE_LICENSE_HEADER_END@
 */

#include <mach/mach_types.h>
#include <mach/machine.h>
#include <mach/policy.h>
#include <mach/sync_policy.h>
#include <mach/thread_act.h>

#include <machine/machine_routines.h>
#include <machine/sched_param.h>
#include <machine/machine_cpu.h>

#include <kern/kern_types.h>
#include <kern/clock.h>
#include <kern/counters.h>
#include <kern/cpu_number.h>
#include <kern/cpu_data.h>
#include <kern/debug.h>
#include <kern/lock.h>
#include <kern/macro_help.h>
#include <kern/machine.h>
#include <kern/misc_protos.h>
#include <kern/processor.h>
#include <kern/queue.h>
#include <kern/sched.h>
#include <kern/sched_prim.h>
#include <kern/syscall_subr.h>
#include <kern/task.h>
#include <kern/thread.h>
#include <kern/wait_queue.h>

#include <vm/pmap.h>
#include <vm/vm_kern.h>
#include <vm/vm_map.h>

#include <mach/sdt.h>

#include <sys/kdebug.h>


#if defined(CONFIG_SCHED_DWRR)

static void
sched_dwrr_init(void);

static void
sched_dwrr_timebase_init(void);

static void
sched_dwrr_processor_init(processor_t processor);

static void
sched_dwrr_pset_init(processor_set_t pset);

static void
sched_dwrr_maintenance_continuation(void);

static thread_t
sched_dwrr_choose_thread(processor_t        processor,
                         int                priority);

static thread_t
sched_dwrr_steal_thread(processor_set_t pset);

static void
sched_dwrr_compute_priority(thread_t    thread,
                            boolean_t   override_depress);

static processor_t
sched_dwrr_choose_processor(processor_set_t     pset,
                            processor_t         processor,
                            thread_t            thread);

static boolean_t
sched_dwrr_processor_enqueue(processor_t processor,
                             thread_t    thread,
                             integer_t   options);

static void
sched_dwrr_processor_queue_shutdown(processor_t processor);

static boolean_t
sched_dwrr_processor_queue_remove(processor_t processor,
                                 thread_t     thread);

static boolean_t
sched_dwrr_processor_queue_empty(processor_t processor);

static boolean_t
sched_dwrr_processor_queue_has_priority(processor_t     processor,
                                        int             priority,
                                        boolean_t       gte);

static boolean_t
sched_dwrr_priority_is_urgent(int priority);

static ast_t
sched_dwrr_processor_csw_check(processor_t processor);

static uint32_t
sched_dwrr_initial_quantum_size(thread_t thread);

static sched_mode_t
sched_dwrr_initial_thread_sched_mode(task_t parent_task);

static boolean_t
sched_dwrr_supports_timeshare_mode(void);

static boolean_t
sched_dwrr_can_update_priority(thread_t thread);

static void
sched_dwrr_update_priority(thread_t thread);

static void
sched_dwrr_lightweight_update_priority(thread_t thread);

static void
sched_dwrr_quantum_expire(thread_t thread);

static boolean_t
sched_dwrr_should_current_thread_rechoose_processor(processor_t processor);

static int
sched_dwrr_processor_runq_count(processor_t processor);

static uint64_t
sched_dwrr_processor_runq_stats_count_sum(processor_t processor);

const struct sched_dispatch_table sched_dwrr_dispatch = {
    sched_dwrr_init,
    sched_dwrr_timebase_init,
    sched_dwrr_processor_init,
    sched_dwrr_pset_init,
    sched_dwrr_maintenance_continuation,
    sched_dwrr_choose_thread,
    sched_dwrr_steal_thread,
    sched_dwrr_compute_priority,
    sched_dwrr_choose_processor,
    sched_dwrr_processor_enqueue,
    sched_dwrr_processor_queue_shutdown,
    sched_dwrr_processor_queue_remove,
    sched_dwrr_processor_queue_empty,
    sched_dwrr_priority_is_urgent,
    sched_dwrr_processor_csw_check,
    sched_dwrr_processor_queue_has_priority,
    sched_dwrr_initial_quantum_size,
    sched_dwrr_initial_thread_sched_mode,
    sched_dwrr_supports_timeshare_mode,
    sched_dwrr_can_update_priority,
    sched_dwrr_update_priority,
    sched_dwrr_lightweight_update_priority,
    sched_dwrr_quantum_expire,
    sched_dwrr_should_current_thread_rechoose_processor,
    sched_dwrr_processor_runq_count,
    sched_dwrr_processor_runq_stats_count_sum,
    sched_traditional_fairshare_init,
    sched_traditional_fairshare_runq_count,
    sched_traditional_fairshare_runq_stats_count_sum,
    sched_traditional_fairshare_enqueue,
    sched_traditional_fairshare_dequeue,
    sched_traditional_fairshare_queue_remove,
    TRUE /* direct_dispatch_to_idle_processors */
};

extern int max_unsafe_quanta;

static uint32_t dwrr_base_quantum;
static uint32_t dwrr_base_quantum_us;
static uint8_t dwrr_quantum_multipliers[NRQS];

static uint64_t sched_dwrr_tick_deadline;

static uint64_t dwrr_global_highest_round;
decl_simple_lock_data(static, dwrr_global_highest_round_lock);

static uint32_t dwrr_migrate_threads_limit;

static void
sched_dwrr_init(void)
{

    dwrr_global_highest_round = 0;
    simple_lock_init(&dwrr_global_highest_round_lock, 0);

    // TODO: Allow using a boot-arg to tune the following variables
    // Calculate the timeslicing quantum in us.
    if (default_preemption_rate < 1)
        default_preemption_rate = 100; // <- DEFAULT_PREEMPTION_RATE
    dwrr_base_quantum_us = (1000 * 1000) / default_preemption_rate;

    // TODO: Allow using a boot-arg to tune this
    // XXX   This currently does nothing...
    dwrr_migrate_threads_limit = 1;
}

static void
sched_dwrr_timebase_init(void)
{
    uint64_t abstime;

    // standard timeslicing quantum
    clock_interval_to_absolutetime_interval(dwrr_base_quantum_us,
                                            NSEC_PER_USEC, &abstime);
    assert((abstime >> 32) == 0 && (uint32_t)abstime != 0);
    dwrr_base_quantum = (uint32_t)abstime;

    int i = 0;
    for(; i < 10; i++)
        dwrr_quantum_multipliers[i] = 1;
    for(; i < 30; i++)
        dwrr_quantum_multipliers[i] = 2;
    for(; i < 50; i++)
        dwrr_quantum_multipliers[i] = 3;
    for(; i < 80; i++)
        dwrr_quantum_multipliers[i] = 4;
    for(; i < 127; i++)
        dwrr_quantum_multipliers[i] = 5;

    // XXX I don't know that these variables actually do anything, but all the
    //     other schedulers set them up.
    max_unsafe_computation = max_unsafe_quanta * dwrr_base_quantum;
    sched_safe_duration = 2 * max_unsafe_quanta * dwrr_base_quantum;

    thread_depress_time = 1 * dwrr_base_quantum;
    default_timeshare_computation = dwrr_base_quantum / 2;
    default_timeshare_constraint = dwrr_base_quantum;

}

static void
sched_dwrr_processor_init(processor_t processor)
{
    struct dwrr_run_queue *runq = &processor->dwrr_runq;
    runq->round_number = dwrr_global_highest_round;

    runq->active_queue = &runq->queue_a;
    runq->expired_queue = &runq->queue_b;

    queue_init(runq->active_queue);
    queue_init(runq->expired_queue);

    runq->count = 0;
}

static void
sched_dwrr_pset_init(processor_set_t pset __unused)
{ }

static volatile uint64_t sched_maintenance_deadline;


static void
sched_dwrr_maintenance_continuation(void)
{
    static uint64_t sched_tick_last_abstime;
    static uint64_t sched_tick_delta;
    static uint64_t sched_tick_max_delta;

    // XXX Copied from traditional scheduler. Is it all still releveant?
    uint64_t sched_tick_ctime = mach_absolute_time();

	if (__improbable(sched_tick_last_abstime == 0)) {
		sched_tick_last_abstime = sched_tick_ctime;
		sched_tick_delta = 1;
	} else {
		sched_tick_delta = ((sched_tick_ctime) - sched_tick_last_abstime) / sched_tick_interval;
		/* Ensure a delta of 1, since the interval could be slightly
		 * smaller than the sched_tick_interval due to dispatch
		 * latencies.
		 */
		sched_tick_delta = MAX(sched_tick_delta, 1);

		/* In the event interrupt latencies or platform
		 * idle events that advanced the timebase resulted
		 * in periods where no threads were dispatched,
		 * cap the maximum "tick delta" at SCHED_TICK_MAX_DELTA
		 * iterations.
		 */
		sched_tick_delta = MIN(sched_tick_delta, SCHED_TICK_MAX_DELTA);

		sched_tick_last_abstime = sched_tick_ctime;
		sched_tick_max_delta = MAX(sched_tick_delta, sched_tick_max_delta);
	}

	/* Add a number of pseudo-ticks corresponding to the elapsed interval
	 * This could be greater than 1 if substantial intervals where
	 * all processors are idle occur, which rarely occurs in practice.
	 */
	sched_tick += sched_tick_delta;

	/*
	 *  Compute various averages.
	 */
	compute_averages(sched_tick_delta);

	assert_wait((event_t)sched_dwrr_maintenance_continuation, THREAD_UNINT);
	thread_block((thread_continue_t)sched_dwrr_maintenance_continuation);
	/*NOTREACHED*/
}


#define get_next_pset(p) \
    (((p)->pset_list != PROCESSOR_SET_NULL) ? (p)->pset_list \
                                            : (p)->node->psets)


static thread_t dwrr_try_get_thread_from_queue(queue_t queue)
{
    thread_t thread = (thread_t)queue_first(queue);
    while(!queue_end(queue, (queue_entry_t)thread))
    {
        if (thread->bound_processor != PROCESSOR_NULL)
        {
            remqueue((queue_entry_t)thread);
            thread->runq = PROCESSOR_NULL;
            return thread;
        }

        thread = (thread_t)queue_next((queue_entry_t)thread);
    }

    return THREAD_NULL;
}

static void dwrr_look_for_threads(processor_t target_processor __unused)
{
    processor_set_t start_pset = target_processor->processor_set;
    processor_set_t current_pset = start_pset;

    thread_t thread = THREAD_NULL;

    do
    {
        processor_t proc = (processor_t)queue_first(&current_pset->active_queue);
        while(!queue_end(&current_pset->active_queue, (queue_entry_t)proc))
        {
            if(proc == target_processor)
            {
                // Don't bother checking the target cpu.
                proc = (processor_t)queue_next((queue_entry_t)proc);
                continue;
            }

            if(!queue_empty(proc->dwrr_runq.active_queue))
                // The active queue is checked for processors in both the
                // current round and the previous round
                thread = dwrr_try_get_thread_from_queue(
                            proc->dwrr_runq.active_queue);

            if(thread == THREAD_NULL &&
               proc->dwrr_runq.round_number < dwrr_global_highest_round &&
               !queue_empty(proc->dwrr_runq.expired_queue))
            {
                // If the processor is a round behind, also check its expired
                // queue.
                thread = dwrr_try_get_thread_from_queue(
                            proc->dwrr_runq.expired_queue);
            }

            if(thread != THREAD_NULL)
            {
                proc->dwrr_runq.count--;
                pset_unlock(current_pset);
                pset_lock(start_pset);

                enqueue(target_processor->dwrr_runq.active_queue,
                        (queue_entry_t)thread);
                SCHED_STATS_RUNQ_CHANGE(&target_processor->dwrr_runq.runq_stats,
                                        target_processor->dwrr_runq.count);
                target_processor->dwrr_runq.count++;
                return;
            }

            proc = (processor_t)queue_next((queue_entry_t)proc);
        }

        processor_set_t next_pset = get_next_pset(current_pset);
        pset_unlock(current_pset);
        current_pset = next_pset;
        pset_lock(current_pset);
        // The list of psets is circular, so exit the loop once we've come back
        // to the start.
    } while(current_pset != start_pset);
}


static thread_t
sched_dwrr_choose_thread(processor_t    processor,
                        int             priority __unused)
{
    struct dwrr_run_queue *runq = &processor->dwrr_runq;

    if(!queue_empty(runq->active_queue))
    {
        thread_t thread = (thread_t)dequeue_head(runq->active_queue);
        SCHED_STATS_RUNQ_CHANGE(&runq->runq_stats, runq->count);
        runq->count--;

        // When we dispatch a thread to be run, mark it with the current round
        // number. When it gets enqueued again, if we're still in the same
        // round it goes into the expired queue.
        thread->round_number = runq->round_number;

        return thread;
    }


    return THREAD_NULL;
}

static thread_t
sched_dwrr_steal_thread(processor_set_t pset)
{
    processor_t processor = current_processor();
    struct dwrr_run_queue *runq = &processor->dwrr_runq;

    thread_t thread = THREAD_NULL;

    if(queue_empty(runq->active_queue))
    {
        pset_unlock(pset);
        simple_lock(&dwrr_global_highest_round_lock);
        pset_lock(pset);

        if(runq->round_number == dwrr_global_highest_round ||
           queue_empty(runq->expired_queue))
        {
            // If we're at the highest round number or we have no threads
            // queued at all, try to migrate threads
            dwrr_look_for_threads(processor);
        }

        if(queue_empty(runq->active_queue) &&
           !queue_empty(runq->expired_queue))
        {
            // We didn't find any threads to steal for other processors, but
            // there are threads in our expire queue, so swap the queues and
            // proceed to the next round.
            void *tmp_queue = runq->active_queue;

            runq->active_queue = runq->expired_queue;
            runq->expired_queue = tmp_queue;

            runq->round_number++;
            if(dwrr_global_highest_round < runq->round_number)
                dwrr_global_highest_round = runq->round_number;
        }
        simple_unlock(&dwrr_global_highest_round_lock);
    }

    if(!queue_empty(runq->active_queue))
    {
        thread = (thread_t)dequeue_head(runq->active_queue);
        SCHED_STATS_RUNQ_CHANGE(&runq->runq_stats, runq->count);
        runq->count--;
    }

    // When we dispatch a thread to be run, mark it with the current round
    // number. When it gets enqueued again, if we're still in the same round
    // it goes into the expired queue.
    if(thread != THREAD_NULL)
        thread->round_number = processor->dwrr_runq.round_number;

    pset_unlock(pset);
    return thread;
}

static void
sched_dwrr_compute_priority(thread_t    thread,
                            boolean_t   override_depress __unused)
{
    set_sched_pri(thread, thread->priority);
}

static processor_t
sched_dwrr_choose_processor(processor_set_t     pset,
                            processor_t         processor,
                            thread_t            thread)
{
    // Reuse the existing choose_processor logic since the hints it relies on
    // managed elsewhere for us anyway.
    return choose_processor(pset, processor, thread);
}

static boolean_t
sched_dwrr_processor_enqueue(processor_t        processor,
                            thread_t            thread,
                            integer_t           options)
{

    struct dwrr_run_queue *runq = &processor->dwrr_runq;


    // If we didn't have any threads enqueued, then go to the current round
    if(queue_empty(runq->active_queue) && queue_empty(runq->expired_queue))
        runq->round_number = dwrr_global_highest_round;

    if(thread->round_number < runq->round_number)
        if(options & SCHED_TAILQ)
            enqueue_tail(runq->active_queue, (queue_entry_t)thread);
        else // options & SCHED_HEADQ
            enqueue_head(runq->active_queue, (queue_entry_t)thread);
    else
        if(options & SCHED_TAILQ)
            enqueue_tail(runq->expired_queue, (queue_entry_t)thread);
        else // options & SCHED_HEADQ
            enqueue_head(runq->expired_queue, (queue_entry_t)thread);

    SCHED_STATS_RUNQ_CHANGE(&runq->runq_stats, runq->count);
    runq->count++;

    // XXX The return type doesn't appear to be checked...
    return TRUE;
}

static void
sched_dwrr_processor_queue_shutdown(processor_t processor)
{
    // It might be a good idea to try enqueue these tasks onto a CPU running in
    // the same round as this one, but I think that this gets called so rarely
    // that it shouldn't matter.

    thread_t thread;
    processor_set_t pset = processor->processor_set;
    queue_head_t tqueue, bqueue;

    queue_init(&tqueue);
    queue_init(&bqueue);


    while(1)
    {
        thread = (thread_t)dequeue(processor->dwrr_runq.active_queue);
        if(thread == THREAD_NULL)
            break;

        if (thread->bound_processor == PROCESSOR_NULL)
            enqueue_tail(&tqueue, (queue_entry_t)thread);
        else
            enqueue_tail(&bqueue, (queue_entry_t)thread);
    }

    while(1)
    {
        thread = (thread_t)dequeue(processor->dwrr_runq.expired_queue);
        if(thread == THREAD_NULL)
            break;

        if (thread->bound_processor == PROCESSOR_NULL)
            enqueue_tail(&tqueue, (queue_entry_t)thread);
        else
            enqueue_tail(&bqueue, (queue_entry_t)thread);
    }

    processor->dwrr_runq.count = 0;

    while ((thread = (thread_t)(void *)dequeue_head(&bqueue)) != THREAD_NULL)
        sched_dwrr_processor_enqueue(processor, thread, SCHED_TAILQ);

    pset_unlock(pset);

    while ((thread = (thread_t)(void *)dequeue_head(&tqueue)) != THREAD_NULL)
    {
        thread_lock(thread);
        thread_setrun(thread, SCHED_TAILQ);
        thread_unlock(thread);
    }
}

static boolean_t
sched_dwrr_processor_queue_remove(processor_t   processor,
                                  thread_t      thread)
{
    struct dwrr_run_queue *runq = &processor->dwrr_runq;

	if (processor == thread->runq) {
		/*
		 *	Thread is on a run queue and we have a lock on
		 *	that run queue.
		 */
		remqueue((queue_entry_t)thread);
        SCHED_STATS_RUNQ_CHANGE(&runq->runq_stats, runq->count);
        runq->count--;
	} else {
		/*
		 *	The thread left the run queue before we could
		 * 	lock the run queue.
		 */
		assert(thread->runq == PROCESSOR_NULL);
		processor = PROCESSOR_NULL;
	}


	return (processor != PROCESSOR_NULL);
}

static boolean_t
sched_dwrr_processor_queue_empty(processor_t processor)
{
    // Don't bother taking the lock; none of the other schedulers do
    return processor->dwrr_runq.count == 0;
}

static boolean_t
sched_dwrr_processor_queue_has_priority(processor_t     processor __unused,
                                         int            priority __unused,
                                         boolean_t      gte __unused)
{
    return TRUE;
}

/* Implement sched_preempt_pri in code */
static boolean_t
sched_dwrr_priority_is_urgent(int priority)
{
    if (priority <= BASEPRI_FOREGROUND)
        return FALSE;

    if (priority < MINPRI_KERNEL)
        return TRUE;

    if (priority >= BASEPRI_PREEMPT)
        return TRUE;

    return FALSE;
}

static ast_t
sched_dwrr_processor_csw_check(processor_t processor)
{
    // Don't bother taking the lock
    if(processor->dwrr_runq.count > 0)
        return AST_PREEMPT;

    return AST_NONE;
}

static uint32_t
sched_dwrr_initial_quantum_size(thread_t thread __unused)
{
    // This is called with thread locked
    if(thread == THREAD_NULL)
        return dwrr_base_quantum;
    else
        return dwrr_base_quantum * dwrr_quantum_multipliers[thread->priority];
}

static sched_mode_t
sched_dwrr_initial_thread_sched_mode(task_t parent_task)
{
    // XXX This code is based on what other schedulers were doing. It really
    //     doesn't do anything though since we don't dynamically update the
    //     priority of threads anyway (ie the meaning of TH_MODE_FIXED).
    if (parent_task == kernel_task)
        return TH_MODE_FIXED;
    else
        return TH_MODE_TIMESHARE;
}

static boolean_t
sched_dwrr_supports_timeshare_mode(void)
{
    return TRUE;
}

static boolean_t
sched_dwrr_can_update_priority(thread_t thread __unused)
{
    return FALSE;
}

static void
sched_dwrr_update_priority(thread_t thread __unused)
{ }

static void
sched_dwrr_lightweight_update_priority(thread_t thread __unused)
{ }

static void
sched_dwrr_quantum_expire(thread_t thread __unused)
{ }

static boolean_t
sched_dwrr_should_current_thread_rechoose_processor(processor_t processor __unused)
{
    return (TRUE);
}

static int
sched_dwrr_processor_runq_count(processor_t processor)
{
    return processor->dwrr_runq.count;
}

static uint64_t
sched_dwrr_processor_runq_stats_count_sum(processor_t processor)
{
    return processor->dwrr_runq.runq_stats.count_sum;
}

#endif /* defined(CONFIG_SCHED_DWRR) */
