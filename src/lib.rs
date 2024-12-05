//! The `stable_matching_distance()` function implements the Gale-Shapley algorithm, as described on page
//! 6 of _Algorithm Design_ by Kleinberg and Tardos.
//!
//! The client supplies a distance function. Preferences are ranked in terms of distance function values,
//! with lower values indicating higher preferences. When calculating preferences, the member of the proposing
//! group is the first argument, and the member of the proposal-receiving group is the second argument.
//!
//! The value function will be called at most twice for each proposer-receiver pair.
//!
//! The function returns a `Vec` containing pairs of indices of elements of the groups. The first element in the pair
//! is an index into the proposing group slice, and the second element is an index into the proposal-receiving group slice.
//!
//! The groups may be of different sizes. In those cases, everyone in the smaller group will have a match with someone
//! in the larger group, but there will be unmatched leftovers in the larger group.
//!
//! In the event of a tie between two proposers competing for the same receiver, the receiver will maintain their current match.
//!
//! Proposers are placed in a queue in order of appearance in the input slice. Each maintains a queue of proposal-receivers, with
//! ties broken by maintaining the order of the input slice. When a proposed match is broken, the proposer is sent to the back
//! of the queue.
//!
//! ```
//! use stable_matching::stable_matching_distance;
//!
//! let group1: Vec<i64> = vec![1, 2, 3, 4, 5];
//! let group2: Vec<i64> = vec![8, 9, 10, 11];
//!
//! let pairs = stable_matching_distance(&group1, &group2, |p1, p2| (p1 - p2).abs());
//! assert_eq!(pairs, vec![(4, 0), (3, 1), (2, 2), (1, 3)]);
//!
//! let pairs = stable_matching_distance(&group2, &group1, |p1, p2| (p1 - p2).abs());
//! assert_eq!(pairs, vec![(3, 1), (2, 2), (1, 3), (0, 4)]);
//! ```
//!
//! If the members of different groups have different preference functions, the `stable_matching_asymmetric()` function
//! may be used to supply these distinct preference functions.
//!
//! In the example below, the receiving group preference is for even numbers to match even, and odd numbers to match odd.
//! Because this implementation will not break a match in the event of a tie in preferences, once a receiver has received a
//! proposal from a proposer with the same evenness/oddness, it will always stick with that proposer.
//!
//! ```
//! use stable_matching::stable_matching_asymmetric;
//!
//! let group1: Vec<i64> = vec![1, 2, 3, 4, 5];
//! let group2: Vec<i64> = vec![8, 9, 10, 11];
//!
//! let pairs = stable_matching_asymmetric(&group1, |p1, p2| (p1 - p2).abs(), &group2, |p1, p2| if p1 % 2 == p2 % 2 {0} else {1});
//! assert_eq!(pairs, vec![(1, 0), (0, 1), (3, 2), (2, 3)]);
//!
//! let group1: Vec<i64> = vec![5, 4, 3, 2, 1];
//! let pairs = stable_matching_asymmetric(&group1, |p1, p2| (p1 - p2).abs(), &group2, |p1, p2| if p1 % 2 == p2 % 2 {0} else {1});
//! assert_eq!(pairs, vec![(1, 0), (0, 1), (3, 2), (2, 3)]);
//! ```

use std::collections::VecDeque;

/// Implements the Gale-Shapley algorithm, as described on page 6 of Algorithm Design by Kleinberg and Tardos.
///
/// Preferences are ranked in terms of distance function values from `value_func(proposer, receiver)`,
/// with lower values indicating higher preferences.
///
/// Returns a `Vec` containing pairs of indices from the input slices, with the proposer index first.
pub fn stable_matching_distance<T, U, N: Ord + Copy, V: Clone + Fn(&T, &U) -> N>(
    proposers: &[T],
    receivers: &[U],
    value_func: V,
) -> Vec<(usize, usize)> {
    stable_matching_asymmetric(proposers, value_func.clone(), receivers, value_func.clone())
}

/// Implements the Gale-Shapley algorithm, as described on page 6 of Algorithm Design by Kleinberg and Tardos.
///
/// Proposer preferences are ranked in terms of distance function values from `proposer_value_func(proposer, receiver)`,
/// with lower values indicating higher preferences. In the event of a tie, preference goes to the proposee earlier in the input slice.
///
/// Proposee preferences are ranked in terms of distance function values from `receiver_value_func(proposer, receiver)`,
/// with lower values again indicating higher preferences. In the event of a tie, preference is to maintain an existing match.
///
/// Returns a `Vec` containing pairs of indices from the input slices, with the proposer index first.
pub fn stable_matching_asymmetric<T, U, N: Ord + Copy, PV: Fn(&T, &U) -> N, RV: Fn(&T, &U) -> N>(
    proposers: &[T],
    proposer_value_func: PV,
    receivers: &[U],
    receiver_value_func: RV,
) -> Vec<(usize, usize)> {
    let mut proposer_prefs = prefs_for_all(proposers, receivers, &proposer_value_func);
    let mut receiver2fiance: Vec<Option<(usize, N)>> = (0..receivers.len()).map(|_| None).collect();
    let mut single_proposers: VecDeque<usize> = (0..proposers.len()).collect();
    while let Some(proposer) = single_proposers.pop_front() {
        if let Some(receiver) = proposer_prefs[proposer].pop_front() {
            if let Some((current, value)) = receiver2fiance[receiver] {
                let proposer_value =
                    receiver_value_func(&proposers[proposer], &receivers[receiver]);
                if proposer_value < value {
                    single_proposers.push_back(current);
                    receiver2fiance[receiver] = Some((proposer, proposer_value))
                } else {
                    single_proposers.push_back(proposer);
                }
            } else {
                receiver2fiance[receiver] = Some((
                    proposer,
                    receiver_value_func(&proposers[proposer], &receivers[receiver]),
                ));
            }
        }
    }
    receiver2fiance
        .iter()
        .enumerate()
        .map(|(w, m)| m.map(|(m, _)| (m, w)))
        .filter_map(|p| p)
        .collect()
}

fn prefs_for_all<T, U, N: Ord + Copy, V: Fn(&T, &U) -> N>(
    people: &[T],
    others: &[U],
    value_func: &V,
) -> Vec<VecDeque<usize>> {
    people
        .iter()
        .map(|p| prefs_for(p, others, value_func))
        .collect()
}

fn prefs_for<T, U, N: Ord + Copy, V: Fn(&T, &U) -> N>(
    person: &T,
    others: &[U],
    value_func: &V,
) -> VecDeque<usize> {
    let mut valuations: Vec<(N, usize)> = others
        .iter()
        .enumerate()
        .map(|(i, t)| (value_func(person, t), i))
        .collect();
    valuations.sort();
    (0..valuations.len()).map(|i| valuations[i].1).collect()
}

#[cfg(test)]
mod tests {
    use crate::{stable_matching_asymmetric, stable_matching_distance};

    #[derive(PartialEq, Eq)]
    struct Man {
        value: i32,
    }

    #[derive(PartialEq, Eq)]
    struct Woman {
        value: i32,
    }

    #[test]
    fn test_different_for_different_types() {
        let men_group = vec![
            Man { value: 1 },
            Man { value: 2 },
            Man { value: 3 },
            Man { value: 4 },
            Man { value: 5 },
        ];

        let women_group = vec![
            Woman { value: 8 },
            Woman { value: 9 },
            Woman { value: 10 },
            Woman { value: 11 },
        ];

        let pairs =
            stable_matching_distance(&men_group, &women_group, |m, w| (m.value - w.value).abs());
        assert_eq!(pairs, vec![(4, 0), (3, 1), (2, 2), (1, 3)]);

        let pairs =
            stable_matching_distance(&women_group, &men_group, |m, w| (m.value - w.value).abs());
        assert_eq!(pairs, vec![(3, 1), (2, 2), (1, 3), (0, 4)]);
    }

    #[test]
    fn test_asymmetric_for_different_types() {
        let men_group = vec![
            Man { value: 1 },
            Man { value: 2 },
            Man { value: 3 },
            Man { value: 4 },
            Man { value: 5 },
        ];

        let women_group = vec![
            Woman { value: 8 },
            Woman { value: 9 },
            Woman { value: 10 },
            Woman { value: 11 },
        ];

        let pairs = stable_matching_asymmetric(
            &men_group,
            |m, w| (m.value - w.value).abs(),
            &women_group,
            |m, w| if m.value % 2 == w.value % 2 { 0 } else { 1 },
        );
        assert_eq!(pairs, vec![(1, 0), (0, 1), (3, 2), (2, 3)]);

        let men_group = vec![
            Man { value: 5 },
            Man { value: 4 },
            Man { value: 3 },
            Man { value: 2 },
            Man { value: 1 },
        ];
        let pairs = stable_matching_asymmetric(
            &men_group,
            |m, w| (m.value - w.value).abs(),
            &women_group,
            |m, w| if m.value % 2 == w.value % 2 { 0 } else { 1 },
        );
        assert_eq!(pairs, vec![(1, 0), (0, 1), (3, 2), (2, 3)]);
    }
}
