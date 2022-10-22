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
    let s = CharList::new().cons('b').cons('a');
    assert_eq!(s.as_ref(), "ab");
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
