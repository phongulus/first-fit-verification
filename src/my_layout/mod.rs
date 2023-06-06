use prusti_contracts::*;

#[extern_spec]
impl usize {
    #[pure]
    #[ensures(self == 0 ==> !result)]
    #[ensures(self == 1 ==> result)]
    #[ensures(self == 2 ==> result)]
    #[ensures(self > 1 && self % 2 != 0 ==> !result)]
    // #[ensures(Self::is_power_of_two(self) ==> Self::is_power_of_two(self * 2))]
    pub fn is_power_of_two(self) -> bool;
}

// #[ensures(align > 0)]
// #[ensures(size > 0)]
#[derive(Clone)]
pub struct Layout {
    align: usize,
    size: usize
}

impl Layout {
    /// Conditions:
    /// - align > 0
    /// - align is a power of 2
    /// - size > 0
    /// - size is a multiple of align
    #[requires(size > 0)]
    #[requires(align > 0)]
    #[requires(usize::is_power_of_two(align))]
    #[requires(size % align == 0)]
    #[ensures(result.size > 0)]
    #[ensures(result.align > 0)]
    // #[ensures(result.align.is_power_of_two())]
    #[ensures(result.size % result.align == 0)]
    pub fn from_size_align(align: usize, size: usize) -> Layout {
        Layout { align, size }
    }

    #[pure]
    // #[requires(self.size > 0)]
    // #[ensures(result > 0)]
    // #[ensures(self.size == old(self.size))]
    pub fn size(&self) -> usize {
        self.size
    }

    #[pure]
    // #[ensures(result > 0)]
    // #[requires(self.align > 0)]
    pub fn align(&self) -> usize {
        self.align
    }
}