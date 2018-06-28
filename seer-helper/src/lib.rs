/// Instructs Seer to make the contents of `var` symbolic.
#[allow(unused_variables)]
pub fn mksym<T>(var: &mut T) {
}

/// This macro must be invoked in the user crate root in order to get formatting to work. It
/// inserts a function `seer_helper_format`. Seer later uses this to get a string representation of
/// variables marked with `mksym`.
#[macro_export]
macro_rules! seer_helper_init {
    () => (
        // prefix to reduce risk of name collisions, since we are messing with the client's
        // namespace.
        use std::fmt::Debug as seer_helper_format_Debug;
        #[allow(dead_code)]
        fn seer_helper_format<T: seer_helper_format_Debug>(t: T) -> String {
            format!("{:?}", t)
        }
    )
}
