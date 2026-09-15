//! Optional instrumentation for differential testing against the Lean model
//! in `model/`.
//!
//! With the `trace` feature enabled, every atomic operation performed by
//! [`RearmBarrier::producer`](crate::RearmBarrier::producer) and
//! [`RearmBarrier::consumer`](crate::RearmBarrier::consumer), plus the
//! non-atomic writes the model tracks, reports an [`Event`] to the hook
//! installed with [`set_hook`]. The hook runs on the thread that performed
//! the operation, right after it, so the per-thread order of events is the
//! program order.
//!
//! Without the feature this module is private and [`record`] is an empty
//! inline function, so the hot path is unchanged.

/// One observable action of a producer or consumer thread.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// The producer wrote job `version` into the job slot (not yet published)
    JobWritten {
        /// Version of the job
        version: usize,
    },
    /// The producer did `fetch_add(1)` on the probe to publish `version`
    Publish {
        /// Version being published
        version: usize,
        /// Value returned by `fetch_add`
        old: usize,
    },
    /// The producer left its spin loop for `version` after loading `value`
    ObserveDone {
        /// Version waited for
        version: usize,
        /// The probe value that ended the spin loop
        value: usize,
    },
    /// Consumer `id` wrote its initial state into its result slot
    StateInit {
        /// Consumer ID
        id: usize,
    },
    /// Consumer `id` left its spin loop for `version` after loading `value`
    ObserveReady {
        /// Consumer ID
        id: usize,
        /// Version waited for
        version: usize,
        /// The probe value that ended the spin loop
        value: usize,
    },
    /// Consumer `id` did `fetch_add(amount)` on ticket `ticket`
    Ticket {
        /// Consumer ID
        id: usize,
        /// Version being completed
        version: usize,
        /// Index into the flat ticket array
        ticket: usize,
        /// Amount added
        amount: usize,
        /// Value returned by `fetch_add`
        old: usize,
    },
    /// Consumer `id` did `fetch_add(1)` on the probe: every worker completed `version`
    Finish {
        /// Consumer ID
        id: usize,
        /// Version completed
        version: usize,
        /// Value returned by `fetch_add`
        old: usize,
    },
}

#[cfg(feature = "trace")]
mod hook {
    use super::Event;
    use core::sync::atomic::{AtomicPtr, Ordering};

    /// The type of a trace hook
    pub type Hook = fn(&Event);

    static HOOK: AtomicPtr<()> = AtomicPtr::new(core::ptr::null_mut());

    /// Install `hook` as the process-wide trace hook. It is called from every
    /// producer and consumer thread, so it must be safe to call concurrently.
    pub fn set_hook(hook: Hook) {
        HOOK.store(hook as *mut (), Ordering::Release);
    }

    /// Remove the trace hook
    pub fn clear_hook() {
        HOOK.store(core::ptr::null_mut(), Ordering::Release);
    }

    #[inline]
    pub(crate) fn record(event: Event) {
        let ptr = HOOK.load(Ordering::Acquire);
        if !ptr.is_null() {
            // SAFETY: the only non-null value ever stored in `HOOK` is a
            // `Hook` cast to a pointer in `set_hook`.
            let hook: Hook = unsafe { core::mem::transmute::<*mut (), Hook>(ptr) };
            hook(&event);
        }
    }
}

#[cfg(feature = "trace")]
pub use hook::{clear_hook, set_hook, Hook};

#[cfg(feature = "trace")]
pub(crate) use hook::record;

/// Without the `trace` feature nothing is recorded
#[cfg(not(feature = "trace"))]
#[inline(always)]
pub(crate) fn record(_event: Event) {}
