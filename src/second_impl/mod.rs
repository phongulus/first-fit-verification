use prusti_contracts::*;
use crate::my_layout::Layout;
use crate::external_spec::{trusted_option::*, trusted_num::*};
use core::cell::RefCell;

const U64_MAX: u64 = 18_446_744_073_709_551_615u64;

// Define some trusted bitwise functions with mathematical assurances that can
// be checked later by Prusti. We can prove manually that these properties hold,
// assuming that Rust's bitwise operations are correct.

// We also have custom Prusti specs on functions `checked_pow` and `trailing_zeros`.

#[trusted]
#[requires(idx < 64)]
#[ensures({
    let p = peek_option(&2u64.checked_pow(idx as u32));
    (old(*u) / p) % 2 == 1 ==> old(*u) == *u
})]
#[ensures({
    let p = peek_option(&2u64.checked_pow(idx as u32));
    (old(*u) / p) % 2 == 0 ==> old(*u) + p == *u
})]
fn set_bit_u64(u: &mut u64, idx: usize) {
    *u = *u | 1 << idx;
}

#[trusted]
#[requires(idx < 64)]
#[ensures({
    let p = peek_option(&2u64.checked_pow(idx as u32));
    (old(*u) / p) % 2 == 0 ==> old(*u) == *u
})]
#[ensures({
    let p = peek_option(&2u64.checked_pow(idx as u32));
    (old(*u) / p) % 2 == 1 ==> old(*u) >= p
})]
#[ensures({
    let p = peek_option(&2u64.checked_pow(idx as u32));
    (old(*u) / p) % 2 == 1 ==> old(*u) - p == *u
})]
fn clear_bit_u64(u: &mut u64, idx: usize) {
    *u = *u & !(1 << idx);
}

#[pure]
#[trusted]
#[requires(idx < 64)]
#[requires(forall (|i: usize| i == idx ==> 2u64.checked_pow(idx as u32).is_some()))]
#[ensures(result ==> (*u / peek_option(&2u64.checked_pow(idx as u32)) % 2 == 1))]
fn is_allocated_u64(u: &u64, idx: usize) -> bool {
    *u & (1 << idx) > 0
}

#[trusted]
#[requires(n <= 64)]
#[ensures(result.trailing_zeros() == n)]
fn make_trailing_zeros_u64(n: u32) -> u64 {
    if n == 64 {0}
    else {
        let p = peek_option(&2u64.checked_pow(n));
        U64_MAX - p + 1
    }
}

// Are the Prusti assertions inside the function enough to guarantee correctness?
// Or do we still need more postconditions?
#[requires(for_size > 0)]
#[requires(capacity > 0)]
#[requires(bitfield.len() > 0)]
#[ensures(bitfield.len() == old(bitfield.len()))]
fn initialize(bitfield: &mut [u64], for_size: usize, capacity: usize) {
    let relevant_bits = core::cmp::min(capacity / for_size, bitfield.len() * 64);

    let mut i: usize = 0;
    while i < bitfield.len() {

        body_invariant!(i < bitfield.len());
        body_invariant!(bitfield.len() == old(bitfield.len()));

        let remaining_bits_opt = relevant_bits.checked_sub(i * 64);
        if let Some(remaining_bits) = remaining_bits_opt {
            if remaining_bits >= 64 {bitfield[i] = 0;}
            else {bitfield[i] = make_trailing_zeros_u64(remaining_bits as u32)}
        } else {bitfield[i] = U64_MAX;}

        prusti_assert!(i * 64 > relevant_bits ==> bitfield[i] == U64_MAX);
        prusti_assert!((i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0);
        prusti_assert!(i * 64 <= relevant_bits && (i + 1) * 64 > relevant_bits ==>
            bitfield[i].trailing_zeros() == peek_option(&remaining_bits_opt) as u32);
        
        i += 1;
    }
}

#[pure]
#[requires(bitfield.len() > 0)]
#[requires(idx < bitfield.len() * 64)]
fn is_allocated(bitfield: &[u64], idx: usize) -> bool {
    is_allocated_u64(&bitfield[idx / 64], idx % 64)
}

#[ensures(!result ==> exists(|i: usize| (bitfield[i] < U64_MAX)))]
#[ensures(forall(|i: usize| (i < bitfield.len() ==> bitfield[i] == U64_MAX)) ==> result)]
#[ensures(result ==> forall(|i: usize| (i < bitfield.len() ==> bitfield[i] == U64_MAX)))]
fn is_full(bitfield: &[u64]) -> bool {
    let mut i = 0;
    while i < bitfield.len() {

        body_invariant!(i < bitfield.len());
        body_invariant!(forall(|j: usize| (j < i ==> bitfield[j] == U64_MAX)));
        
        if bitfield[i] < U64_MAX {return false}
        
        prusti_assert!(bitfield[i] == U64_MAX);
        
        i += 1;
    }
    true
}

#[requires(bitfield.len() > 0)]
#[requires(relevant_bits < bitfield.len() * 64)]
// #[ensures(result ==> forall(|i: usize| (i * 64 <= relevant_bits ==> forall(|j: usize| (j < i ==> bitfield[j] == 0)))))]
// #[ensures(forall(|i: usize| (i < bitfield.len() && (i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0)) ==> result)]
// #[ensures(result ==> forall(|i: usize| (i < bitfield.len() && (i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0)))]
fn all_free(bitfield: &[u64], relevant_bits: usize) -> bool {
    let mut i = 0;
    while i < bitfield.len() {

        body_invariant!(i < bitfield.len());
        body_invariant!(bitfield.len() == old(bitfield.len()));
        body_invariant!(i * 64 <= relevant_bits ==> forall(|j: usize| (j < i ==> bitfield[j] == 0)));
        
        let remaining_bits_opt = relevant_bits.checked_sub(i * 64);
        if let Some(remaining_bits) = remaining_bits_opt {
            if remaining_bits >= 64 {if bitfield[i] != 0 {return false;}}
            else {if bitfield[i].trailing_zeros() != remaining_bits as u32 {return false;}}
        } else {}

        // Same assertions as in `initialize()`
        // prusti_assert!(i * 64 > relevant_bits ==> bitfield[i] == U64_MAX); // Verify that bits outside of relevant_bits are not modified?
        prusti_assert!((i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0);
        prusti_assert!((i + 1) * 64 <= relevant_bits ==> forall(|j: usize| (j <= i ==> bitfield[j] == 0)));
        prusti_assert!(i * 64 <= relevant_bits && (i + 1) * 64 > relevant_bits ==>
            bitfield[i].trailing_zeros() == peek_option(&remaining_bits_opt) as u32);

        i += 1;
    }
    true
}

#[requires(idx < bitfield.len() * 64)]
#[ensures({
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let p = peek_option(&(2u64.checked_pow(bit_idx as u32)));
    (old(bitfield[base_idx]) / p) % 2 == 0 ==> bitfield[base_idx] == old(bitfield[base_idx])
})]
#[ensures({
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let p = peek_option(&(2u64.checked_pow(bit_idx as u32)));
    (old(bitfield[base_idx]) / p) % 2 == 1 ==> bitfield[base_idx] < old(bitfield[base_idx])
})]
#[ensures({
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let p = peek_option(&(2u64.checked_pow(bit_idx as u32)));
    (old(bitfield[base_idx]) / p) % 2 == 1 ==>
        old(bitfield[base_idx]) - bitfield[base_idx] == p
})]
fn clear_bit(bitfield: &mut [u64], idx: usize) {
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let mut b_u64 = bitfield[base_idx];
    clear_bit_u64(&mut b_u64, bit_idx);
    bitfield[base_idx] = b_u64;

    // The above should be equivalent to this line below, but this cannot be
    // verified due to Prusti's limitations.
    // clear_bit_u64(&mut bitfield[idx / 64], idx % 64);
}

#[requires(idx < bitfield.len() * 64)]
#[ensures({
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let p = peek_option(&(2u64.checked_pow(bit_idx as u32)));
    (old(bitfield[base_idx]) / p) % 2 == 1 ==> bitfield[base_idx] == old(bitfield[base_idx])
})]
#[ensures({
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let p = peek_option(&(2u64.checked_pow(bit_idx as u32)));
    (old(bitfield[base_idx]) / p) % 2 == 0 ==> bitfield[base_idx] > old(bitfield[base_idx])
})]
#[ensures({
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let p = peek_option(&(2u64.checked_pow(bit_idx as u32)));
    (old(bitfield[base_idx]) / p) % 2 == 0 ==>
        bitfield[base_idx] - old(bitfield[base_idx]) == p
})]
fn set_bit(bitfield: &mut [u64], idx: usize) {
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let mut b_u64 = bitfield[base_idx];
    set_bit_u64(&mut b_u64, bit_idx);
    bitfield[base_idx] = b_u64;

    // The above should be equivalent to this line below, but this cannot be
    // verified due to Prusti's limitations.
    // set_bit_u64(&mut bitfield[idx / 64], idx % 64);
}

// #[pure]
#[requires(u < U64_MAX)]
#[ensures(result < 64)]
#[ensures({
    let p = peek_option(&2u64.checked_pow(result));
    u / p % 2 == 0
})]
#[ensures({
    let p = peek_option(&2u64.checked_pow(result));
    u % p == p - 1
})]
#[ensures(!is_allocated_u64(&u, result as usize))]
fn first_fit_idx(u: u64) -> u32 {
    u.trailing_ones()
}

#[requires(layout.size() > 0)]
#[requires(layout.align() > 0)]
#[requires(u < U64_MAX)]
pub fn first_fit_in_u64 (
    u: u64,
    base_idx: usize,
    base_addr: usize,
    layout: Layout,
    page_size: usize,
    metadata_size: usize
) -> Option<(usize, usize)> {
    let first_free = first_fit_idx(u) as usize;
    let idx = base_idx * 64 + first_free;
    let offset = idx * layout.size();
    let addr = base_addr + offset;
    if offset > (page_size - metadata_size - layout.size()) && addr % layout.align() == 0 {
        Some((idx, addr))
    } else {None}
}

#[requires(layout.size() > 0)]
#[requires(layout.align() > 0)]
fn first_fit(
    bitfield: &[u64],
    base_addr: usize,
    layout: Layout,
    page_size: usize,
    metadata_size: usize
) -> Option<(usize, usize)> {
    let mut base_idx = 0;
    while base_idx < bitfield.len() {
        if bitfield[base_idx] < U64_MAX {
            return first_fit_in_u64(bitfield[base_idx], base_idx, base_addr, layout, page_size, metadata_size)
        }
        base_idx += 1;
    }
    None
}

pub struct TrustedBitfield8{bitfield: [u64; 8]}

impl TrustedBitfield8 {
    pub fn new(for_size: usize, capacity: usize) -> Option<Self> {
        if for_size > 0 && capacity > 0 && for_size < capacity {
            let mut bitfield = TrustedBitfield8{ bitfield: [0, 0, 0, 0, 0, 0, 0, 0] };
            let () = initialize(&mut bitfield.bitfield, for_size, capacity);
            Some(bitfield)
        } else {None}
    }

    #[requires(for_size > 0)]
    #[requires(capacity > 0)]
    #[requires(self.bitfield.len() > 0)]
    pub fn initialize(&mut self, for_size: usize, capacity: usize) {initialize(&mut self.bitfield, for_size, capacity)}

    #[requires(layout.size() > 0)]
    #[requires(layout.align() > 0)]
    fn first_fit(
        &self,
        base_addr: usize,
        layout: Layout,
        page_size: usize,
        metadata_size: usize,
    ) -> Option<(usize, usize)> {
        first_fit(&self.bitfield, base_addr, layout, page_size, metadata_size)
    }

    #[requires(self.bitfield.len() > 0)]
    #[requires(idx < self.bitfield.len() * 64)]
    fn is_allocated(&self, idx: usize) -> bool {is_allocated(&self.bitfield, idx)}

    #[requires(idx < self.bitfield.len() * 64)]
    fn set_bit(&mut self, idx: usize) {set_bit(&mut self.bitfield, idx)}

    #[requires(idx < self.bitfield.len() * 64)]
    fn clear_bit(&mut self, idx: usize) {clear_bit(&mut self.bitfield, idx)}

    fn is_full(&self) -> bool {is_full(&self.bitfield)}

    #[requires(self.bitfield.len() > 0)]
    #[requires(relevant_bits < self.bitfield.len() * 64)]
    fn all_free(&self, relevant_bits: usize) -> bool {all_free(&self.bitfield, relevant_bits)}
}

// impl TrustedBitfield8 {
//     #[requires(for_size > 0)]
//     #[requires(capacity > 0)]
//     #[requires(self.0.len() > 0)]
//     #[ensures(self.0.len() == old(self.0.len()))]
//     fn initialize(&mut self, for_size: usize, capacity: usize) {
//         let bitfield = &mut self.0;
//         let relevant_bits = core::cmp::min(capacity / for_size, bitfield.len() * 64);
//         let mut i: usize = 0;
//         while i < bitfield.len() {
//             // body_invariant!(b)
//             body_invariant!(i < bitfield.len());
//             bitfield[i] = 
//                 if (i + 1) * 64 <= relevant_bits {0}
//                 else if i * 64 < relevant_bits
//                     {U64_MAX - peek_option(&(2u64.checked_pow((relevant_bits - i * 64) as u32))) + 1}
//                 else {U64_MAX};
//             i += 1;
//         }
//     }
// }

// trait Bitfield {
//     #[requires(for_size > 0)]
//     #[requires(capacity > 0)]
//     #[requires(self.len() > 0)]
//     // #[ensures(old(self).len() == self.len())]
//     fn initialize(&mut self, for_size: usize, capacity: usize);
//     // fn first_fit(
//     //     &self,
//     //     base_addr: usize,
//     //     layout: Layout,
//     //     page_size: usize,
//     //     metadata_size: usize,
//     // ) -> Option<(usize, usize)>;
//     // fn is_allocated(&self, idx: usize) -> bool;
//     // fn set_bit(&self, idx: usize);
//     // fn clear_bit(&self, idx: usize);
//     // fn is_full(&self) -> bool;
//     // fn all_free(&self, relevant_bits: usize) -> bool;
// }

// #[refine_trait_spec]
// impl Bitfield for [u64] {
//     #[requires(for_size > 0)]
//     #[requires(capacity > 0)]
//     // #[requires(self.get_ref().len() == old(self).get_ref().len())]
//     #[requires(self.len() > 0)]
//     #[ensures(self.len() == old(self.len()))]
//     fn initialize(&mut self, for_size: usize, capacity: usize) {
//         let relevant_bits = core::cmp::min(capacity / for_size, self.len() * 64);
//         // prusti_assert!(relevant_bits > 0);
//         let mut i: usize = 0;
//         while i < self.len() {
//             body_invariant!(self.len() == old(self.len()));
//             // body_invariant!(i > 0 && i * 64 >= relevant_bits ==> self[i] == U64_MAX);
//             self[i] = 
//                 if (i + 1) * 64 <= relevant_bits {0}
//                 else if i * 64 < relevant_bits
//                     {U64_MAX - peek_option(&(2u64.checked_pow((relevant_bits - i * 64) as u32))) + 1}
//                 else {U64_MAX};
//             i += 1;
//         }
//     }
// }

// pub trait Tr {
    
// }



// trait Bitfield {
//     const SIZE: usize;
//     fn new() -> Self;

//     #[pure]
//     fn get_ref(&self) -> &[u64];

//     fn get_mut_ref(&mut self) -> &mut [u64];

//     // #[pure]
//     // fn get_size(&self) -> usize;
// }

// pub struct TrustedBitfield8([u64; TrustedBitfield8::SIZE]);

// impl Bitfield for TrustedBitfield8 {
//     const SIZE: usize = 8;

//     #[pure]
//     fn get_ref(&self) -> &[u64] {&(self.0)}

//     fn new() -> Self {TrustedBitfield8([0, 0, 0, 0, 0, 0, 0, 0])}
//     fn get_mut_ref(&mut self) -> &mut [u64] {&mut self.0}

//     // #[pure]
//     // #[trusted]
//     // #[ensures(forall (|i: usize| (i < result ==> self.bitfield.)))]
//     // fn get_size(&self) -> usize {self.bitfield.len()}
// }

// trait TrustedBitfield: Bitfield {
//     // #[pure]
//     // fn base_length(&self) -> usize {
//     //     self.get_ref().len()
//     // }

//     #[requires(for_size > 0)]
//     #[requires(capacity > 0)]
//     // #[requires(self.get_ref().len() == old(self).get_ref().len())]
//     fn initialize(&mut self, for_size: usize, capacity: usize) {
//         let bitfield = self.get_mut_ref();
//         let relevant_bits = core::cmp::min(capacity / for_size, bitfield.len() * 64);

//         let mut i: usize = 0;
//         while i < bitfield.len() {
//             bitfield[i] = 
//                 if (i + 1) * 64 <= relevant_bits {0}
//                 else if i * 64 < relevant_bits
//                     {U64_MAX - peek_option(&(2u64.checked_pow((relevant_bits - i * 64) as u32))) + 1}
//                 else {U64_MAX};
//             i += 1;
//         }
//     }

//     // #[requires(idx / 64 < self.get_size())]
//     fn is_allocated(&self, idx: usize) -> Option<bool> {
//         let base_idx = idx / 64;
//         let bit_idx = idx % 64;
//         let p = peek_option(&(2u64.checked_pow(bit_idx as u32)));
//         let bitfield = self.get_ref();
//         if base_idx < bitfield.len() {
//             Some((bitfield[base_idx] / p) % 2 == 1)
//         } else {None}

//         // This is more elegant than the chunk above but Prusti wouldn't take it so ¯\_(ツ)_/¯ ;-;
//         // self.get_ref().get(base_idx).map(|u| (*u / p) % 2 == 1)
//     }

//     fn is_full(&self) -> bool {
//         let bitfield = self.get_ref();
//         let mut i: usize = 0;
//         while i < bitfield.len() {
//             if bitfield[i] != U64_MAX {return false};
//             i += 1;
//         }
//         true
//     }

//     fn is_empty(&self) -> bool {
//         let bitfield = self.get_ref();
//         let mut i: usize = 0;
//         while i < bitfield.len() {
//             if bitfield[i] != 0 {return false};
//             i += 1;
//         }
//         true
//     }

//     #[requires(relevant_bits < self.get_ref().len())]
//     fn all_free(&self, relevant_bits: usize) -> bool {
//         let bitfield = self.get_ref();
//         let mut i: usize = 0;
//         while i < bitfield.len() {
//             if ((i + 1) * 64 <= relevant_bits && bitfield[i] != 0) ||
//                 (i * 64 < relevant_bits && bitfield[i] != U64_MAX -
//                     peek_option(&(2u64.checked_pow((relevant_bits - i * 64) as u32))) + 1)
//                 {return false};
//             i += 1;
//         }
//         true
//     }



//     // fn set_bit(&self, idx: usize) {
//     //     let base_idx = idx / 64;
//     //     let bit_idx = idx % 64;
//     //     self[base_idx].fetch_or(1 << bit_idx, Ordering::Relaxed);
//     // }

//     // fn is_allocated(&self, idx: usize) {
//     //     let base
//     // }
//     // fn first_fit(
//     //     &self,
//     //     base_addr: usize,
//     //     layout: Layout,
//     //     page_size: usize,
//     //     metadata_size: usize,
//     // ) -> Option<(usize, usize)>;
//     // fn is_allocated(&self, idx: usize) -> bool;
//     // fn set_bit(&self, idx: usize);
//     // fn clear_bit(&self, idx: usize);
//     // fn is_full(&self) -> bool;
//     // fn all_free(&self, relevant_bits: usize) -> bool;
// }

// impl TrustedBitfield for TrustedBitfield8 {}

// impl TrustedBitfield for T where (T: Bitfield) {

// }

// impl TrustedBitfield {
//     fn new(arr: [u64]) -> Self {
//         TrustedBitfield { bitfield: Box::new(RefCell::new(value)) }
//     }
// }

// #[requires(for_size > 0)]
// #[requires(capacity > 0)]
// #[requires(bitfield.len() > 0)]
// #[ensures(bitfield.len() == old(bitfield.len()))]
// // #[ensures(forall(|j: usize| ((j + 1) * 64 < capacity / for_size && j < bitfield.len() ==> bitfield[j] == 0)))]
// fn initialize(bitfield: &mut [u64], for_size: usize, capacity: usize) {
//     let relevant_bits = core::cmp::min(capacity / for_size, bitfield.len() * 64);
//     let mut i: usize = 0;
//     while i < bitfield.len() {
//         body_invariant!(bitfield.len() == old(bitfield.len()));
//         body_invariant!(i * 64 < (i + 1) * 64);
//         body_invariant!((i + 1) * 64 > 0);
//         if (i + 1) * 64 <= relevant_bits {
//             bitfield[i] = 0;
//         } else if i * 64 < relevant_bits {
//             let bits_to_flip = (relevant_bits - i * 64) as u32;
//             // prusti_assert!(bits_to_flip > 0);
//             let p = peek_option(&2u64.checked_pow(bits_to_flip));
//             bitfield[i] = U64_MAX - p + 1;
//         } else {
//             bitfield[i] = U64_MAX;
//         }
//         prusti_assert!((i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0);
//         prusti_assert!(i * 64 >= relevant_bits ==> bitfield[i] == U64_MAX);
//         prusti_assert!(i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==> 0 < bitfield[i] && bitfield[i] < U64_MAX);
//         // prusti_assert!(i * 64 < relevant_bits ==> forall(|j: usize| (j < i ==> (j + 1) * 64 <= relevant_bits)));
//         // prusti_assert!(forall(|j: usize| (j < i ==> bitfield[j] == old(bitfield[j]))));
//         // prusti_assert!(i * 64 < relevant_bits ==> forall(|j: usize| (j < i ==> bitfield[j] == 0)));
//         i += 1;
//     }
// }

// #[pure]
// #[requires(n < 64)]
// // #[ensures(n == 0 && u == 0 ==> result == 0)]
// // #[ensures(n == 0 && u == U64_MAX ==> result == 64)]
// // #[ensures(n == 0 && u < U64_MAX ==> result < 64)]
// fn my_trailing_ones_aux (n: u32, u: u64) -> u32 {
//     let p = peek_option(&2u64.checked_pow(n));
//     if (u / p) % 2 == 0 {n}
//     else if n == 63 {64}
//     else {my_trailing_ones_aux(n + 1, u)}
// }

// // #[pure]
// // #[ensures(u == 0 ==> result == 0)]
// // #[ensures(u == U64_MAX ==> result == 64)]
// // #[ensures(u < U64_MAX ==> result < 64)]
// fn my_trailing_ones (u: u64) -> u32 {
//     my_trailing_ones_aux(0, u)
// }