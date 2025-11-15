//! Miscellaneous helpers for zk-lisp crates.
//!
//! Currently only contains small experimental utilities;
//! real shared helpers should migrate here as the
//! workspace evolves.

pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
