

#[macro_export]
/// Create a **Bmap** from a list of key-value pairs
///
/// ## Example
///
/// ```
/// #[macro_use]
/// extern crate bmap;
/// # fn main() {
///
/// let foo = bmap!{
///     "a" => 1,
///     "b" => 2,
/// };
/// assert_eq!(foo["a"], 1);
/// assert_eq!(foo["b"], 2);
/// assert_eq!(foo.get("c"), None);
/// # }
/// ```
macro_rules! bmap {
    // trailing comma case
    ($($key:expr => $value:expr,)+) => (bmap!($($key => $value),+));
    
    ( $($key:expr => $value:expr),* ) => {
        {
            let mut _map = $crate::Bmap::new();
            $(
                _map.insert($key, $value);
            )*
            _map
        }
    };
}
