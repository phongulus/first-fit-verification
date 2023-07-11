use std::sync::atomic::Ordering;
use prusti_contracts::*;

pub trait AtomicU64WrapperTrait {
    #[pure]
    #[trusted]
    fn load(&self, order: Ordering) -> u64;

    #[trusted]
    #[ensures(self.load(order) == val)]
    fn store(&mut self, val: u64, order: Ordering);
}