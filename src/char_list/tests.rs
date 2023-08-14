use crate::pq_rc::pq_rc_cell::new_counts::{current_live_allocs, reset_counts, total_new_count};

use super::CharList;
use assert2::{assert, check, let_assert};
use std::iter;

#[test]
fn mem_test_cdr_down() {
    let s3: CharList = CharList::from("abc");

    assert!(s3.backing_string().len() == 3);

    let_assert!(Some((a, s2)) = s3.car_cdr());
    assert!(a == 'a');
    assert!(s2 == "bc");

    assert!(s3.backing_string().len() == 3);

    let_assert!(Some((b, s1)) = s2.car_cdr());
    assert!(b == 'b');
    assert!(s1 == "c");

    drop(s3);
    assert!(s1.backing_string().len() == 2);

    let_assert!(Some((c, s0)) = s1.car_cdr());
    assert!(c == 'c');
    assert!(s0.is_empty());
    assert!(s0 == "");

    assert!(s0.car_cdr() == None);

    drop(s2);
    drop(s1);
    assert!(s0.backing_string().len() == 0);
}

#[test]
fn mem_test_cons_up() {
    let empty: CharList = CharList::new();
    assert!(empty.is_empty());
    assert!(empty.backing_string() == &"");

    let icon = empty.cons_str("icon");
    assert!(icon == "icon");
    assert!(empty.backing_string() == &"icon");

    let nomicon = icon.cons_str("nom");
    assert!(nomicon == "nomicon");
    assert!(empty.backing_string() == &"nomicon");

    let rustonomicon = nomicon.cons_str("rusto");
    assert!(rustonomicon == "rustonomicon");
    assert!(empty.backing_string() == &"rustonomicon");

    let nominomicon = nomicon.cons_str("nomi");
    assert!(nominomicon == "nominomicon");
    assert!(empty.backing_string() == &"rustonomicon");
    assert!(nominomicon.backing_string() == &"nominomicon");
}

static NOUNS: [&str; 3] = ["candy", "ghost", "costume"];
fn noun() -> Box<dyn Iterator<Item = CharList>> {
    Box::new(
        NOUNS
            .into_iter()
            .map(CharList::from)
            .collect::<Vec<_>>()
            .into_iter(),
    )
}

static VERBS: [&str; 3] = ["chased", "stalked", "frightened"];
fn verb() -> Box<dyn Iterator<Item = CharList>> {
    Box::new(
        VERBS
            .into_iter()
            .map(CharList::from)
            .collect::<Vec<_>>()
            .into_iter(),
    )
}

static DETERMINERS: [&str; 5] = ["the", "that", "my", "your", "some"];
fn determiner() -> Box<dyn Iterator<Item = CharList>> {
    Box::new(
        DETERMINERS
            .into_iter()
            .map(CharList::from)
            .collect::<Vec<_>>()
            .into_iter(),
    )
}

fn sentence_forward() -> Box<dyn Iterator<Item = CharList>> {
    Box::new(determiner().flat_map(|d1| {
        noun().flat_map(move |n1| {
            let d1 = d1.clone();
            verb().flat_map(move |v| {
                let d1 = d1.clone();
                let n1 = n1.clone();
                determiner().flat_map(move |d2| {
                    let d1 = d1.clone();
                    let n1 = n1.clone();
                    let v = v.clone();
                    noun().flat_map(move |n2| {
                        let d1 = d1.clone();
                        let n1 = n1.clone();
                        let v = v.clone();
                        let d2 = d2.clone();
                        iter::once(
                            n2.cons(' ')
                                .cons_str(d2)
                                .cons(' ')
                                .cons_str(v)
                                .cons(' ')
                                .cons_str(n1)
                                .cons(' ')
                                .cons_str(d1),
                        )
                    })
                })
            })
        })
    }))
}

fn simple_sentence_backwards() -> Box<dyn Iterator<Item = CharList>> {
    Box::new(noun().flat_map(move |n| {
        determiner().flat_map(move |d| {
            let n = n.clone();
            iter::once(n.cons(' ').cons_str(d))
        })
    }))
}

fn sentence_backward() -> Box<dyn Iterator<Item = CharList>> {
    Box::new(noun().flat_map(|n2| {
        determiner().flat_map(move |d2| {
            let n2 = n2.clone();
            verb().flat_map(move |v| {
                let n2 = n2.clone();
                let d2 = d2.clone();
                noun().flat_map(move |n1| {
                    let n2 = n2.clone();
                    let d2 = d2.clone();
                    let v = v.clone();
                    determiner().flat_map(move |d1| {
                        let n2 = n2.clone();
                        let d2 = d2.clone();
                        let v = v.clone();
                        let n1 = n1.clone();
                        iter::once(
                            n2.cons(' ')
                                .cons_str(d2)
                                .cons(' ')
                                .cons_str(v)
                                .cons(' ')
                                .cons_str(n1)
                                .cons(' ')
                                .cons_str(d1),
                        )
                    })
                })
            })
        })
    }))
}

macro_rules! test_nonterminal_expansions {
        ($($test_name:ident { $nonterminal_fn_name:ident => $word_groups:expr })+) => {
            $(
                #[test]
                fn $test_name() {
                    let words_used: Vec<_> = $word_groups.concat();

                    let mut live_char_lists = vec![];
                    reset_counts();

                    for s in $nonterminal_fn_name() {
                        let n = current_live_allocs();
                        live_char_lists.push(n);

                        for word in s.as_str().split_ascii_whitespace() {
                            check!(
                                words_used.contains(&word),
                                "{word:?} isn't in {words_used:?}.\n(s = {s:?})"
                            );
                        }
                    }

                    // check!(polynomial_degree(&allocs) == Some(1));

                    let avg_live =
                        live_char_lists.iter().copied().sum::<usize>() / live_char_lists.len();
                    check!(avg_live <= words_used.len());

                    // Due to the way these nested `flat_map`s are set up, we expect `CharList`s to
                    // be allocated according to the product of the lengths of the word groups.
                    // In a real application, things could probably be setup more efficiently.
                    let num_words_generated: usize = $word_groups.iter().map(|g| g.len()).product();

                    const REASONABLE_FACTOR_FOR_UPPER_BOUND_ON_LIVE_ALLOC_COUNT: usize = 2;
                    check!(current_live_allocs() <= num_words_generated * REASONABLE_FACTOR_FOR_UPPER_BOUND_ON_LIVE_ALLOC_COUNT);

                    const REASONABLE_FACTOR_FOR_UPPER_BOUND_ON_TOTAL_NEW_COUNT: usize = 2;
                    check!(total_new_count() <= num_words_generated * REASONABLE_FACTOR_FOR_UPPER_BOUND_ON_TOTAL_NEW_COUNT);
                }
            )+
        };
    }

test_nonterminal_expansions! {
    generate_simple_backwards {
        simple_sentence_backwards => [&DETERMINERS[..], &NOUNS[..]]
    }

    generate_forward {
        sentence_forward => [
            &DETERMINERS[..], &NOUNS[..], &VERBS[..], &DETERMINERS[..], &NOUNS[..]
        ]
    }

    generate_backward {
        sentence_backward => [
            &DETERMINERS[..], &NOUNS[..], &VERBS[..], &DETERMINERS[..], &NOUNS[..]
        ]
    }
}

#[cfg(test)]
mod parser_use_case {
    use super::*;
    use assert2::assert;

    fn character(target: char) -> impl Fn(&CharList) -> Option<(char, CharList)> {
        move |i| {
            let (ch, i) = i.car_cdr()?;
            (ch == target).then_some((ch, i))
        }
    }

    fn many0<T>(
        p: impl Fn(&CharList) -> Option<(T, CharList)>,
    ) -> impl Fn(&CharList) -> Option<(Vec<T>, CharList)> {
        move |i| {
            let mut i = i.clone();
            let mut ts = vec![];

            while !i.is_empty() {
                match p(&i) {
                    Some((t, rem)) => {
                        ts.push(t);
                        i = rem;
                    }
                    None => break,
                }
            }

            Some((ts, i))
        }
    }

    fn or<T, P1, P2>(p1: P1, p2: P2) -> impl Fn(&CharList) -> Option<(T, CharList)>
    where
        P1: Fn(&CharList) -> Option<(T, CharList)>,
        P2: Fn(&CharList) -> Option<(T, CharList)>,
    {
        move |i| p1(i).or_else(|| p2(i))
    }

    fn ws0(i: &CharList) -> Option<((), CharList)> {
        let (_, i) = many0(character(' '))(i)?;
        Some(((), i))
    }

    fn ident(i: &CharList) -> Option<(Token, CharList)> {
        let (ident, i) = i.split_after_nonempty_prefix(char::is_alphabetic)?;
        Some((Token::Ident(ident.to_owned()), i))
    }

    fn nat(i: &CharList) -> Option<(Token, CharList)> {
        let (n, i) = i.split_after_nonempty_prefix(char::is_numeric)?;
        let n = n.parse::<u64>().ok()?;
        Some((Token::Nat(n), i))
    }

    #[derive(Debug, PartialEq, Eq)]
    enum Token {
        Ident(String),
        Nat(u64),
    }

    #[test]
    fn little_parser() {
        use crate::pq_rc::pq_rc_cell::new_counts::{reset_counts, total_new_count};

        reset_counts();

        let i = CharList::from("one 2 three 456");

        let words = many0(|i: &CharList| {
            let (tok, i) = or(ident, nat)(i)?;
            let (_, i) = ws0(&i)?;
            Some((tok, i))
        });

        let (w, i) = words(&i).unwrap();

        assert!(i == "");

        assert!(
            w == vec![
                Token::Ident("one".to_owned()),
                Token::Nat(2),
                Token::Ident("three".to_owned()),
                Token::Nat(456),
            ]
        );

        // Only one call to `PqRcCell::new`.
        // This makes sense because, for instance, `nom` doesn't need to allocate
        // new strings, it works but slicing subslices of subslices of subslices.
        assert!(total_new_count() == 1);
    }
}

/// Returns `None` if inconculsive (ran out of data points).
#[cfg(test)]
fn polynomial_degree(ys: &[i128]) -> Option<usize>
// fn polynomial_degree<Num>(ys: &[Num]) -> Option<usize>
// where
//     Num: std::ops::Sub<Output = Num> + std::cmp::Eq + Clone + Copy,
{
    let mut degree = 0;

    let mut ys = ys.to_vec();
    let mut diffs = ys.clone();

    fn all_same(ys: &[impl std::cmp::Eq]) -> Option<bool> {
        (ys.len() > 1).then_some(())?;
        let (first, rest) = ys.split_first()?;
        Some(rest.iter().all(|y| y == first))
    }

    while !all_same(&diffs)? {
        diffs = std::iter::zip(&ys[..], &ys[1..])
            .map(|(&y1, &y2)| y2.checked_sub(y1))
            .collect::<Option<_>>()?;

        ys.clone_from(&diffs);
        degree += 1;
    }

    Some(degree)
}

#[test]
fn test_polynomial_degree() {
    use assert2::assert;
    let ys: Vec<i128> = (0..100)
        .map(|x| 2 * x * x * x * x - x * x * x - 5 * x * x + 18 * x + 32)
        .collect();
    assert!(polynomial_degree(&ys) == Some(4));
}
