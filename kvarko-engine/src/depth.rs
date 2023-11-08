use std::iter;
use std::iter::Once;
use std::ops::RangeInclusive;
use std::time::{Duration, Instant};

/// The type used to identify the depth of a tree search. A depth of 0 indicates
/// immediate base evaluation. To find a playable move, a depth of at least 1 is
/// required.
pub type Depth = u32;

/// A trait for strategies to decide at which depths to search over a potential
/// iterative deepening process.
pub trait DepthStrategy {

    /// An iterator over [Depth]s used in iterative tree search.
    type DepthIterator: Iterator<Item = Depth>;

    /// Creates a [Self::DepthIterator] used in iterative tree search in the
    /// order they are returned. Once the iterator is finished, no more searches
    /// will be done and the result is returned. The returned iterator must
    /// contain at least one depth greater than 0.
    fn depth_iterator(&self) -> Self::DepthIterator;
}

/// A [DepthStrategy] which searches at the target depth directly.
pub struct DirectDepth {
    depth: Depth
}

impl DirectDepth {

    /// Creates a new direct depth strategy which searches at the given depth
    /// directly.
    ///
    /// # Arguments
    ///
    /// * `depth`: The target depth. Must be greater than 0.
    pub fn new(depth: Depth) -> DirectDepth {
        if depth == 0 {
            panic!("depth cannot be 0");
        }

        DirectDepth { depth }
    }
}

impl DepthStrategy for DirectDepth {

    type DepthIterator = Once<Depth>;

    fn depth_iterator(&self) -> Once<Depth> {
        iter::once(self.depth)
    }
}

/// A [DepthStrategy] which searches at incremental depths from 1 to a given
/// target depth.
pub struct IterativeDeepeningToDepth {
    depth: Depth
}

impl IterativeDeepeningToDepth {

    /// Creates a new iterative-deepening-to-depth strategy which searches at
    /// depths 1 to the given depth in ascending order.
    ///
    /// # Arguments
    ///
    /// * `depth`: The target depth, i.e. the highest searched depth
    /// (inclusive). Must be greater than 0.
    pub fn new(depth: Depth) -> IterativeDeepeningToDepth {
        if depth == 0 {
            panic!("depth cannot be 0");
        }

        IterativeDeepeningToDepth { depth }
    }
}

impl DepthStrategy for IterativeDeepeningToDepth {

    type DepthIterator = RangeInclusive<Depth>;

    fn depth_iterator(&self) -> RangeInclusive<Depth> {
        1..=self.depth
    }
}

/// The [DepthStrategy::DepthIterator] for [IterativeDeepeningForDuration].
pub struct DeepenUntilDepthIterator {
    deepen_until: Instant,
    current: Depth
}

impl Iterator for DeepenUntilDepthIterator {

    type Item = Depth;

    fn next(&mut self) -> Option<Depth> {
        if Instant::now() <= self.deepen_until || self.current == 0 {
            self.current += 1;
            Some(self.current)
        }
        else {
            None
        }
    }
}

/// A [DepthStrategy] which searches at incremental depths starting from 1 until
/// a given duration has expired. If the duration expired before the first
/// iteration, a search at depth 1 is ordered.
#[derive(Clone)]
pub struct IterativeDeepeningForDuration {

    /// Before this duration has elapsed from the start of the iteration, a
    /// higher depth will always be ordered by the strategy. Afterwards, the
    /// iterator will return `None` unless it is the first iteration.
    pub deepen_for: Duration
}

impl DepthStrategy for IterativeDeepeningForDuration {

    type DepthIterator = DeepenUntilDepthIterator;

    fn depth_iterator(&self) -> DeepenUntilDepthIterator {
        DeepenUntilDepthIterator {
            deepen_until: Instant::now() + self.deepen_for,
            current: 0
        }
    }
}

#[cfg(test)]
mod tests {

    use std::thread;

    use kernal::prelude::*;

    use super::*;

    #[test]
    fn direct_depth_returns_given_depth_once() {
        let depth_strategy = DirectDepth::new(2);

        let mut depth_iterator = depth_strategy.depth_iterator();

        assert_that!(depth_iterator.next()).contains(2);
        assert_that!(depth_iterator.next()).is_none();
    }

    #[test]
    fn direct_depth_requires_depth_greater_zero() {
        assert_that!(|| DirectDepth::new(0)).panics();
    }

    #[test]
    fn iterative_deepening_to_depth_returns_only_one_if_max_depth_is_one() {
        let depth_strategy = IterativeDeepeningToDepth::new(1);

        let mut depth_iterator = depth_strategy.depth_iterator();

        assert_that!(depth_iterator.next()).contains(1);
        assert_that!(depth_iterator.next()).is_none();
    }

    #[test]
    fn iterative_deepening_to_depth_returns_all_depths_from_zero_to_max_depth() {
        let depth_strategy = IterativeDeepeningToDepth::new(3);

        let depths = depth_strategy.depth_iterator().collect::<Vec<_>>();

        assert_that!(depths).contains_exactly_in_given_order([1, 2, 3]);
    }

    #[test]
    fn iterative_deepening_to_depth_requires_depth_greater_zero() {
        assert_that!(|| IterativeDeepeningToDepth::new(0)).panics();
    }

    #[test]
    fn iterative_deepening_for_duration_returns_increasing_depths_while_in_duration() {
        let depth_strategy = IterativeDeepeningForDuration {
            deepen_for: Duration::from_secs(10)
        };

        let mut depth_iterator = depth_strategy.depth_iterator();

        assert_that!(depth_iterator.next()).contains(1);
        assert_that!(depth_iterator.next()).contains(2);
    }

    #[test]
    fn iterative_deepening_for_duration_does_not_return_higher_depth_once_after_duration() {
        let deepen_for = Duration::from_millis(5);
        let depth_strategy = IterativeDeepeningForDuration {
            deepen_for
        };

        let mut depth_iterator = depth_strategy.depth_iterator();
        depth_iterator.next();

        thread::sleep(deepen_for);

        assert_that!(depth_iterator.next()).is_none();
    }

    #[test]
    fn iterative_deepening_for_duration_returns_at_least_one() {
        let deepen_for = Duration::from_millis(5);
        let depth_strategy = IterativeDeepeningForDuration {
            deepen_for
        };

        let mut depth_iterator = depth_strategy.depth_iterator();

        thread::sleep(deepen_for);

        assert_that!(depth_iterator.next()).contains(1);
    }
}
