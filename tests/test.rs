#![cfg(test)]

use assert2::{assert, check, let_assert};
use test_log::test;

use char_list::CharList;

#[test]
fn construct_destruct() {
    CharList::new();
}

#[test]
fn construct_cmp() {
    let s = CharList::new();
    assert!(s == "");
}

#[test]
fn cons_1() {
    let s = CharList::new().cons('a');
    assert!(s == "a");
}

#[test]
fn cons_2() {
    let s0 = CharList::new();
    let s1 = s0.cons('z');
    let s2 = s1.cons('y');
    let s3 = s2.cons('x');
    assert!(s0.len() == 0);
    assert!(s0 == "");
    assert!(s1.len() == 1);
    assert!(s1 == "z");
    assert!(s2.len() == 2);
    assert!(s2 == "yz");
    assert!(s3.len() == 3);
    assert!(s3 == "xyz");
}

#[test]
fn cons_hirigana() {
    let entire = "いろはにほへとちりぬるを";
    let mut s = CharList::new();
    for ch in entire.chars().rev() {
        s = s.cons(ch);
    }
    assert!(s == entire);
}

#[test]
fn from_str() {
    let text = "いろはにほへとちりぬるを";
    let s = CharList::from(text);
    assert!(s == text);
}

#[test]
fn car_cdr_simple() {
    let s = CharList::from("a");
    let_assert!(Some((head, tail)) = s.car_cdr(), "s = {s:?}");
    check!(head == 'a');
    check!(tail == "");
}

#[test]
fn car_cdr_long() {
    let abc = CharList::from("abc");

    let_assert!(Some((a, bc)) = abc.car_cdr());
    assert!(a == 'a');
    assert!(bc == "bc");

    let_assert!(Some((b, c)) = bc.car_cdr());
    assert!(b == 'b');
    assert!(c == "c");

    let_assert!(Some((c_char, empty)) = c.car_cdr(), "c = {c:?}");
    assert!(c_char == 'c');
    assert!(empty.is_empty());
    assert!(empty == "");

    assert!(empty.car_cdr() == None);
}

#[test]
fn cons_str_backwards() {
    let mut sentence = CharList::new();

    const WORDS: &[&str] = &["In", "the", "town", "where", "I", "was", "born"];

    for word in WORDS.iter().rev() {
        sentence = sentence.cons_str(word).cons(' ');
    }

    let_assert!(Some((' ', sentence)) = sentence.car_cdr());
    assert!(sentence == "In the town where I was born");
}

#[test]
fn tree_of_char_lists() {
    let mammal = CharList::from("mammal");
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
