// use prusti_contracts::*;
use crate::external_spec::{trusted_option::*};

// #[extern_spec]
// impl usize {
//     #[pure]
//     #[ensures(self == 0 ==> !result)]
//     #[ensures(self == 1 ==> result)]
//     #[ensures(self == 2 ==> result)]
//     #[ensures(self > 1 && self % 2 != 0 ==> !result)]
//     // #[ensures(Self::is_power_of_two(self) ==> Self::is_power_of_two(self * 2))]
//     pub fn is_power_of_two(self) -> bool;
// }

// #[invariant(self.align > 0)]
// #[invariant(self.size > 0)]
// #[invariant(self.align.is_power_of_two())]
// #[invariant(self.size % self.align == 0)]
// #[derive(Clone, Copy)]
// pub struct Layout {
//     align: usize,
//     size: usize
// }

// #[pure]
// pub fn layout_size(layout: &Layout) -> usize {
//     layout.size
// }

// pub fn from_size_align(align: usize, size: usize) -> Option<Layout> {
//     if size > 0 && align > 0 && align.is_power_of_two() && size % align == 0 {
//         Some(Layout { align, size })
//     } else {None}
// }

// #[pure]
// pub fn layout_align(layout: &Layout) -> usize {
//     layout.align
// }

// impl Layout {
//     /// Conditions:
//     /// - align > 0
//     /// - align is a power of 2
//     /// - size > 0
//     /// - size is a multiple of align
//     /// The postconditions underneath are now guaranteed by type invariants on the Layout struct.
//     // #[ensures(result.is_some() ==> {
//     //     size > 0 && align > 0 && align.is_power_of_two() && size % align == 0
//     // })]
//     // #[ensures(result.is_some() ==> {
//     //     peek_option(&result).size > 0 &&
//     //     peek_option(&result).align > 0 &&
//     //     peek_option(&result).align.is_power_of_two() &&
//     //     peek_option(&result).size % peek_option(&result).align == 0
//     // })]
//     fn from_size_align(align: usize, size: usize) -> Option<Layout> {
//         if size > 0 && align > 0 && align.is_power_of_two() && size % align == 0 {
//             Some(Layout { align, size })
//         } else {None}
//     }

//     #[pure]
//     fn size(&self) -> usize {
//         self.size
//     }

//     #[pure]
//     fn align(&self) -> usize {
//         self.align
//     }
// }