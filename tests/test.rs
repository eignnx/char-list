#![cfg(test)]

use assert2::{assert, check, let_assert};
use test_log::test;

use char_list::CharListSegment;

#[test]
fn construct_destruct() {
    CharListSegment::new();
}

#[test]
fn construct_cmp() {
    let s = CharListSegment::new();
    assert!(s == "");
}

#[test]
fn cons_1() {
    let s = CharListSegment::new().cons('a');
    assert!(s == "a");
}

#[test]
fn cons_2() {
    let s0 = CharListSegment::new();
    let s1 = s0.cons('z');
    let s2 = s1.cons('y');
    let s3 = s2.cons('x');
    assert!(s0.len().unwrap() == 0);
    assert!(s0 == "");
    assert!(s1.len().unwrap() == 1);
    assert!(s1 == "z");
    assert!(s2.len().unwrap() == 2);
    assert!(s2 == "yz");
    assert!(s3.len().unwrap() == 3);
    assert!(s3 == "xyz");
}

#[test]
fn cons_hirigana() {
    let entire = "いろはにほへとちりぬるを";
    let mut s = CharListSegment::new();
    for ch in entire.chars().rev() {
        s = s.cons(ch);
    }
    assert!(s == entire);
}

#[test]
fn from_str() {
    let text = "いろはにほへとちりぬるを";
    let s = CharListSegment::from(text);
    assert!(s == text);
}

#[test]
fn car_cdr_simple() {
    let s = CharListSegment::from("a");
    let_assert!(Ok(Some((head, tail))) = s.car_cdr(), "s = {s:?}");
    check!(head == 'a');
    check!(tail == "");
}

#[test]
fn car_cdr_long() {
    let abc = CharListSegment::from("abc");

    let_assert!(Ok(Some((a, bc))) = abc.car_cdr());
    assert!(a == 'a');
    assert!(bc == "bc");

    let_assert!(Ok(Some((b, c))) = bc.car_cdr());
    assert!(b == 'b');
    assert!(c == "c");

    let_assert!(Ok(Some((c_char, empty))) = c.car_cdr(), "c = {c:?}");
    assert!(c_char == 'c');
    assert!(empty.is_empty().unwrap());
    assert!(empty == "");

    assert!(matches!(empty.car_cdr(), Ok(None)));
}

#[test]
fn cons_str_backwards() {
    let mut sentence = CharListSegment::new();

    const WORDS: &[&str] = &["In", "the", "town", "where", "I", "was", "born"];

    for word in WORDS.iter().rev() {
        sentence = sentence.cons_str(word).cons(' ');
    }

    let_assert!(Ok(Some((' ', sentence))) = sentence.car_cdr());
    assert!(sentence == "In the town where I was born");
}

#[test]
fn tree_of_char_lists() {
    let mammal = CharListSegment::from("mammal");
    {
        let dog = mammal.cons_str("dog < ");
        let poodle = dog.cons_str("poodle < ");
        assert!(mammal == "mammal");
        assert!(dog == "dog < mammal");
        assert!(poodle == "poodle < dog < mammal");
    }
    let cat = mammal.cons_str("cat < ");
    assert!(mammal == "mammal");
    assert!(cat == "cat < mammal");
}
