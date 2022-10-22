use char_list::CharList;

#[test]
fn construct_destruct() {
    CharList::new();
}

#[test]
fn construct_cmp() {
    let s = CharList::new();
    assert_eq!(s.as_ref(), "");
}

#[test]
fn cons_1() {
    let s = CharList::new().cons('a');
    assert_eq!(s.as_ref(), "a");
}

#[test]
fn cons_2() {
    let s0 = CharList::new();
    let s1 = s0.cons('z');
    let s2 = s1.cons('y');
    let s3 = s2.cons('x');
    assert_eq!(s0.len(), 0);
    assert_eq!(s0.as_ref(), "");
    assert_eq!(s1.len(), 1);
    assert_eq!(s1.as_ref(), "z");
    assert_eq!(s2.len(), 2);
    assert_eq!(s2.as_ref(), "yz");
    assert_eq!(s3.len(), 3);
    assert_eq!(s3.as_ref(), "xyz");
}

#[test]
fn cons_hirigana() {
    let entire = "いろはにほへとちりぬるを";
    let mut s = CharList::new();
    for ch in entire.chars().rev() {
        s = s.cons(ch);
    }
    assert_eq!(s.as_ref(), entire);
}
