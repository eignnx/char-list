#[macro_export]
macro_rules! log {
    ($($arg:tt)*) => {
        #[cfg(feature = "trace-verbose")] {
            eprint!("\x1B[33m");
            eprint!("@[{}:{}]\t", file!(), line!());
            eprint!($($arg)*);
            eprintln!("\x1B[0m");
        }
    };
}

#[test]
fn test_log() {
    #[allow(unused)]
    let local = "QWERTY";
    log!("This is a test with value `{}`, and local {local}!", 123);
}
