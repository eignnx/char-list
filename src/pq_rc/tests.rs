use super::*;

fn slice_it(x: &PqRc<String, usize>) -> &str {
    &x[0..PqRc::priority(&x)]
}

#[test]
fn new_then_drop() {
    PqRc::new(String::new(), 0);
}

#[test]
fn empty_is_eq_to_empty() {
    let x = PqRc::new(String::new(), 0);
    assert_eq!(PqRc::ref_count(&x), 1);
    assert_eq!(x, "");
}

#[test]
fn new_then_clone_then_drop() {
    let x = PqRc::new(String::new(), 0);
    let y = x.clone();
    assert_eq!(PqRc::ref_count(&x), 2);
    assert_eq!(slice_it(&x), "");
    assert_eq!(PqRc::ref_count(&y), 2);
    assert_eq!(slice_it(&y), "");
}

#[test]
fn immut_mutate() {
    let x = PqRc::new(String::new(), 0);
    let y = unsafe {
        PqRc::mutate_or_clone_raising_prio(
            &x,
            |s| {
                s.push('Z');
                1
            },
            |_| (1, "Z".to_owned()),
        )
    };

    assert_eq!(slice_it(&x), "");
    assert_eq!(slice_it(&y), "Z");

    assert_eq!(PqRc::ref_count(&x), 2);
    assert_eq!(PqRc::ref_count(&y), 2);
}
