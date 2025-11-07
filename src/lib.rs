pub mod air;
pub mod error;
pub mod layout;
pub mod pi;
pub mod poseidon;
pub mod schedule;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn schedule_shapes() {
        let n = 32;
        let cols = schedule::build_periodic_selectors(n);

        assert!(!cols.is_empty());

        for c in cols.iter() {
            assert_eq!(c.len(), n);
        }
    }
}
