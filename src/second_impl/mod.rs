use prusti_contracts::*;
use crate::external_spec::{trusted_option::*, trusted_num::*};
use core::cell::RefCell;

const U64_MAX: u64 = 18_446_744_073_709_551_615u64;

// Define some trusted bitwise functions with mathematical assurances that can
// be checked later by Prusti. We can prove manually that these properties hold,
// assuming that Rust's bitwise operations are correct.

// We also have custom Prusti specs on functions `checked_pow` and `trailing_zeros`.

/// We have several numerical properties associated with checking/setting/clearing
/// a bit inside of a `u64`, which contains 64 bits. We index each bit from right to
/// left starting at 0 up to 63 inclusive, assuming a little endian system. Although
/// the functions themselves use bitwise operations, we can tell Prusti the numerical
/// properties using the `trusted` function declaration followed by postconditions.
/// 
/// We start with the following observations - pending formally written proofs:
/// 
///     - Flipping a bit at index i is equivalent to adding or subtracting 2^i to/from u.
///     This is how unsigned integers are represented in base 2 / binary.
/// 
///     - Given some bit at index i, all previous bits (bits at indices less than i) add up
///     to 2^i - 1 when all flipped (we can understand this intuitively in base 10 as the number
///     immediately before, say, 1000 being 999). When we have i = 0, then 2^i - 1 = 2^0 - 1 = 0.
/// 
///     - Given some bit at index i, flipping any subsequent bit (bits at indices greater
///     than i) is adding or subtracting an even multiple of 2^i ("even multiple" here meaning
///     the number can be written as 2k * 2^i - is there a better term for this?). This is
///     because adding to the index i is equivalent to multiplying the 2^i term by 2 one or
///     multiple times.
/// 
/// Given the above observations, we come up with the properties for flipping and checking the
/// bits of a `u64` u:
/// 
///     - Setting a bit at index i is equivalent to adding 2^i to u, assuming that bit is
///     currently 0.
/// 
///     - Clearing a bit at index i is equivalent to subtracting 2^i from u, assuming that bit
///     is currently 1.
/// 
///     - To check whether a bit at index i is flipped, we check whether the quotient of
///     the euclidean division of u by 2^i is divisible by 2. If yes, the bit is 0, and if
///     not, the bit is 1.
/// 
///     - To check whether a bit at index i is the first free bit, i.e. the first 0 bit,
///     We check whether the remainder of the euclidean division of u by 2^i is 2^i - 1.
///     This works for i = 0 as well, since 2^0 = 1 and a division by 1 is always 0 - the
///     index 0 is always first if it is free. 

// TODO: Verify the trusted properties on paper or with Verus

#[trusted]
#[requires(idx < 64)]  // Valid index needed.
#[ensures({  // If the bit is previously set, there should be no change to u.
    let p = peek_option(&2u64.checked_pow(idx as u32));
    (old(*u) / p) % 2 == 1 ==> old(*u) == *u
})]
#[ensures({  // If the bit is not set, u should be changed to u + 2^idx.
    let p = peek_option(&2u64.checked_pow(idx as u32));
    (old(*u) / p) % 2 == 0 ==> old(*u) + p == *u
})]
#[ensures({  // Regardless of whether u is updated or not, the bit should be 1 when the function returns.
    let p = peek_option(&2u64.checked_pow(idx as u32));
    (*u / p) % 2 == 1
})]
fn set_bit_u64(u: &mut u64, idx: usize) {
    *u = *u | (1 << idx);
}

#[trusted]
#[requires(idx < 64)]  // Valid index needed.
#[ensures({  // If the bit is previously cleared, there should be no change to u.
    let p = peek_option(&2u64.checked_pow(idx as u32));
    (old(*u) / p) % 2 == 0 ==> old(*u) == *u
})]
#[ensures({  // If the bit is set, u should be changed to u - 2^idx.
    let p = peek_option(&2u64.checked_pow(idx as u32));
    (old(*u) / p) % 2 == 1 ==> old(*u) - p == *u
})]
#[ensures({  // Regardless of whether u is updated or not, the bit should be 0 when the function returns.
    let p = peek_option(&2u64.checked_pow(idx as u32));
    (*u / p) % 2 == 0
})]
fn clear_bit_u64(u: &mut u64, idx: usize) {
    *u = *u & !(1 << idx);
}

#[pure]
#[trusted]
#[requires(idx < 64)]  // Valid index needed.
#[requires(forall (|i: usize| i == idx ==> 2u64.checked_pow(i as u32).is_some()))]  // Ditto
#[ensures(result ==> (*u / peek_option(&2u64.checked_pow(idx as u32)) % 2 == 1))]  // Check for allocated
#[ensures(!result ==> (*u / peek_option(&2u64.checked_pow(idx as u32)) % 2 == 0))]  // Check for not allocated
fn is_allocated_u64(u: &u64, idx: usize) -> bool {
    *u & (1 << idx) > 0
}

#[trusted]
#[requires(n <= 64)]  // Ensures valid input: we can have 64 trailing zeros at most for a 64-bit number.
#[ensures(result.trailing_zeros() == n)]  
#[ensures(result == U64_MAX <==> n == 0)]  // Cannot be enforced as part of trailing_zeros
fn make_trailing_zeros_u64(n: u32) -> u64 {
    if n == 64 {0}
    else {
        let p = peek_option(&2u64.checked_pow(n));
        U64_MAX - p + 1
    }
}

#[requires(bitfield.len() > 0)]
#[requires(relevant_bits > 0)]
#[requires(relevant_bits <= bitfield.len() * 64)]  // Relevant bits within array bounds.
#[ensures(bitfield.len() == old(bitfield.len()))]  // No change to the length of the u64 array.
#[ensures(forall(|i: usize| ((i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0)))]  // All relevant bits in u64's before the one containing the final relevant bit must be set to 0.
#[ensures(forall(|i: usize| (i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==> bitfield[i].trailing_zeros() as usize == relevant_bits % 64)))]  // The u64 containing the final relevant bit is set correctly.
#[ensures(forall(|i: usize| (i < bitfield.len() && i * 64 >= relevant_bits ==> bitfield[i] == U64_MAX)))] // All bits after the u64 containing the final relevant bit must be set to allocated.
fn initialize(bitfield: &mut [u64], relevant_bits: usize) {
    let mut i: usize = 0;
    while i < bitfield.len() {

        body_invariant!(i < bitfield.len());
        body_invariant!(bitfield.len() == old(bitfield.len()));
        body_invariant!(i * 64 < relevant_bits ==> forall(|j: usize| j < i ==> bitfield[j] == 0));
        body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));
        body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| (j * 64 >= relevant_bits && j < i ==> bitfield[j] == U64_MAX)));
        body_invariant!(i * 64 >= relevant_bits ==>
            forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits && j < i ==>
                bitfield[j].trailing_zeros() as usize == relevant_bits % 64
            ))
        );

        let bit_idx = i * 64;
        if bit_idx <= relevant_bits {
            let remaining_bits = relevant_bits - bit_idx;
            prusti_assert!(remaining_bits == relevant_bits - bit_idx);
            prusti_assert!(relevant_bits % 64 == (relevant_bits - bit_idx) % 64);
            prusti_assert!(relevant_bits % 64 == remaining_bits % 64);
            prusti_assert!(remaining_bits < 64 ==> relevant_bits % 64 == remaining_bits);
            if remaining_bits >= 64 {bitfield[i] = 0;}
            else {
                bitfield[i] = make_trailing_zeros_u64(remaining_bits as u32);
                prusti_assert!(bitfield[i].trailing_zeros() as usize == remaining_bits);
                prusti_assert!(bitfield[i].trailing_zeros() as usize == relevant_bits % 64);
            }
        } else {bitfield[i] = U64_MAX;}

        prusti_assert!(i * 64 >= relevant_bits ==> bitfield[i] == U64_MAX);
        prusti_assert!((i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0);
        prusti_assert!(i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==>
            bitfield[i].trailing_zeros() == (relevant_bits - bit_idx) as u32);

        i += 1;
    }
    prusti_assert!(i > 0);
    prusti_assert!(i == bitfield.len());
    prusti_assert!(forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));
    prusti_assert!(forall(|j: usize| (j * 64 >= relevant_bits && j < bitfield.len() ==> bitfield[j] == U64_MAX)));
    prusti_assert!(
        forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==>
            bitfield[j].trailing_zeros() as usize == relevant_bits % 64
        ))
    );

}

#[pure]
#[requires(bitfield.len() > 0)]
fn is_allocated(bitfield: &[u64], idx: usize) -> Option<bool> {
    if idx < bitfield.len() * 64 {
        Some(is_allocated_u64(&bitfield[idx / 64], idx % 64))
    } else {None}
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
#[requires(relevant_bits <= bitfield.len() * 64)]
#[requires(relevant_bits > 0)]
#[ensures(result ==> forall(|i: usize| ((i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0)))]
#[ensures(result ==> forall(|i: usize| (
    i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==>
        bitfield[i].trailing_zeros() as usize == relevant_bits % 64
)))]
fn all_free(bitfield: &[u64], relevant_bits: usize) -> bool {
    let mut i = 0;
    while i < bitfield.len() {

        body_invariant!(i < bitfield.len());
        body_invariant!(bitfield.len() == old(bitfield.len()));
        body_invariant!(i * 64 <= relevant_bits ==> forall(|j: usize| (j < i ==> bitfield[j] == 0)));

        body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));
        body_invariant!(i * 64 >= relevant_bits ==>
            forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits && j < i ==>
                bitfield[j].trailing_zeros() as usize == relevant_bits % 64
            ))
        );

        let bit_idx = i * 64;
        if bit_idx <= relevant_bits {
            let remaining_bits = relevant_bits - bit_idx;
            if remaining_bits >= 64 {if bitfield[i] != 0 {return false;}}
            else {if bitfield[i].trailing_zeros() != remaining_bits as u32 {return false;}}
        } else {}

        // prusti_assert!(i * 64 >= relevant_bits ==> bitfield[i] == U64_MAX);  // Verify that bits outside of relevant_bits are not modified?
        prusti_assert!((i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0);
        prusti_assert!(i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==>
            bitfield[i].trailing_zeros() == (relevant_bits - bit_idx) as u32);

        i += 1;
    }

    prusti_assert!(i > 0);
    prusti_assert!(i == bitfield.len());
    prusti_assert!(forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));
    prusti_assert!(
        forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==>
            bitfield[j].trailing_zeros() as usize == relevant_bits % 64
        ))
    );

    true
}

#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the bitfield isn't changed if the bit
    let base_idx = idx / 64;               // is already 0.
    let bit_idx = idx % 64;
    let p = peek_option(&(2u64.checked_pow(bit_idx as u32)));
    (old(bitfield[base_idx]) / p) % 2 == 0 ==> bitfield[base_idx] == old(bitfield[base_idx])
})]
#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the bitfield value decreased if the bit
    let base_idx = idx / 64;               // was previously set to 1.
    let bit_idx = idx % 64;
    let p = peek_option(&(2u64.checked_pow(bit_idx as u32)));
    (old(bitfield[base_idx]) / p) % 2 == 1 ==> bitfield[base_idx] < old(bitfield[base_idx])
})]
#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the correct bit was flipped.
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let p = peek_option(&(2u64.checked_pow(bit_idx as u32)));
    (old(bitfield[base_idx]) / p) % 2 == 1 ==>
        old(bitfield[base_idx]) - bitfield[base_idx] == p
})]
fn clear_bit(bitfield: &mut [u64], idx: usize) -> Option<bool> {
    if idx >= bitfield.len() * 64 {return None}
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let mut b_u64 = bitfield[base_idx];
    clear_bit_u64(&mut b_u64, bit_idx);
    let ret = bitfield[base_idx] == b_u64;
    bitfield[base_idx] = b_u64;
    Some(ret)

    // The above should be equivalent to this line below, but this cannot be
    // verified due to Prusti's limitations.
    // clear_bit_u64(&mut bitfield[idx / 64], idx % 64);
}

#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the bitfield isn't changed if the bit
    let base_idx = idx / 64;               // is already set.
    let bit_idx = idx % 64;
    let p = peek_option(&(2u64.checked_pow(bit_idx as u32)));
    (old(bitfield[base_idx]) / p) % 2 == 1 ==> bitfield[base_idx] == old(bitfield[base_idx])
})]
#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the bitfield value increased if the bit
    let base_idx = idx / 64;               // wasn't previously set.
    let bit_idx = idx % 64;
    let p = peek_option(&(2u64.checked_pow(bit_idx as u32)));
    (old(bitfield[base_idx]) / p) % 2 == 0 ==> bitfield[base_idx] > old(bitfield[base_idx])
})]
#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the correct bit was flipped.
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let p = peek_option(&(2u64.checked_pow(bit_idx as u32)));
    (old(bitfield[base_idx]) / p) % 2 == 0 ==>
        bitfield[base_idx] - old(bitfield[base_idx]) == p
})]
fn set_bit(bitfield: &mut [u64], idx: usize) -> Option<bool> {
    if idx >= bitfield.len() * 64 {return None}
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let mut b_u64 = bitfield[base_idx];
    set_bit_u64(&mut b_u64, bit_idx);
    let ret = bitfield[base_idx] == b_u64;
    bitfield[base_idx] = b_u64;
    Some(ret)

    // The above should be equivalent to this line below, but this cannot be
    // verified due to Prusti's limitations.
    // set_bit_u64(&mut bitfield[idx / 64], idx % 64);
}

#[requires(u < U64_MAX)]
#[ensures(result < 64)]  // Correct range for result
#[ensures({
    let p = peek_option(&2u64.checked_pow(result));
    u / p % 2 == 0  // Check that the result index is availble
})]
#[ensures({
    let p = peek_option(&2u64.checked_pow(result));
    u % p == p - 1  // Check that the result index is the first one available (all previous indices allocated)
})]
#[ensures(!is_allocated_u64(&u, result as usize))]  // Same as first check (do we need this?)
fn first_fit_idx(u: u64) -> u32 {
    u.trailing_ones()
}

#[requires(layout_size > 0)]
#[requires(layout_align > 0)]
#[requires(u < U64_MAX)]
#[ensures(result.is_some() ==> {  // The returned index should within the bounds of the current u64.
    let (idx, addr) = peek_option(&result);
    idx >= base_idx * 64 && idx < base_idx * 64 + 64
})]
#[ensures(result.is_some() ==> {  // The index is mapped to the correct address.
    let (idx, addr) = peek_option(&result);
    addr == base_addr + idx * layout_size
})]
#[ensures(result.is_some() ==> {  // Check that the returned address does not overlap with metadata. 
    let (idx, addr) = peek_option(&result);
    addr - base_addr <= page_size - metadata_size - layout_size && addr % layout_align == 0
})]
pub fn first_fit_in_u64 (
    u: u64,
    base_idx: usize,
    base_addr: usize,
    layout_size: usize,
    layout_align: usize,
    page_size: usize,
    metadata_size: usize
) -> Option<(usize, usize)> {
    let first_free = first_fit_idx(u) as usize;
    let idx = base_idx * 64 + first_free;
    let offset = idx * layout_size;
    let addr = base_addr + offset;
    if offset <= (page_size - metadata_size - layout_size) && addr % layout_align == 0 {
        Some((idx, addr))
    } else {None}
}

#[requires(layout_size > 0)]
#[requires(layout_align > 0)]
#[ensures(result.is_some() ==> {  // Check that the returned index is within range and that the address is correct.
    let (idx, addr) = peek_option(&result);
    idx < bitfield.len() * 64 && addr == base_addr + idx * layout_size
})]
#[ensures(result.is_some() ==> {  // Check that the returned address does not overlap with metadata.
    let (idx, addr) = peek_option(&result);
    addr - base_addr <= page_size - metadata_size - layout_size && addr % layout_align == 0
})]
#[ensures(result.is_some() ==> {  // Ensure that all u64 before the returned index is full. The result being the first free bit of its u64 is already guaranteed by `first_fit_in_u64`.
    let (idx, addr) = peek_option(&result);
    let base_idx = idx / 64;
    forall(|i: usize| i < base_idx ==> bitfield[i] == U64_MAX)
})]
#[ensures(forall(|i: usize| i < bitfield.len() ==> bitfield[i] == U64_MAX) ==> !result.is_some())]
fn first_fit(
    bitfield: &[u64],
    base_addr: usize,
    layout_size: usize,
    layout_align: usize,
    page_size: usize,
    metadata_size: usize
) -> Option<(usize, usize)> {
    let mut base_idx = 0;
    while base_idx < bitfield.len() {

        body_invariant!(base_idx < bitfield.len());
        body_invariant!(forall(|i: usize| i < base_idx ==> bitfield[i] == U64_MAX));  // All previous u64 must have max value

        if bitfield[base_idx] < U64_MAX {
            return first_fit_in_u64(bitfield[base_idx], base_idx, base_addr, layout_size, layout_align, page_size, metadata_size)
        }

        prusti_assert!(bitfield[base_idx] == U64_MAX);

        base_idx += 1;
    }

    prusti_assert!(forall(|i: usize| i < bitfield.len() ==> bitfield[i] == U64_MAX));

    None
}


// This code allows for easy expansion of the TrustedBitfield structs. To have trusted bitfields with longer or shorter lengths
// than 8 * 64, simply copy paste the struct and its `impl` block and rename and change size where needed. The new trusted bitfields
// will have the same correctness guarantees as TrustedBitfield8.

#[invariant(self.relevant_bits <= self.bitfield.len() * 64)]  // The number of used bits cannot exceed the maximum number of available bits.
#[invariant(self.relevant_bits > 0)]  // The number of used bits should be more than 0.
#[invariant(self.layout_align > 0)]
#[invariant(self.layout_size > 0)]
#[invariant(self.layout_align.is_power_of_two())]
#[invariant(self.layout_size % self.layout_align == 0)]
// #[invariant(self.initialized ==> forall(|i: usize| i < self.bitfield.len() && i * 64 >= self.relevant_bits ==> self.bitfield[i] == U64_MAX))]
pub struct TrustedBitfield8 {  // Change name for other bitfield types
    bitfield: [u64; TrustedBitfield8::SIZE],  // Change name for other bitfield sizes
    relevant_bits: usize,
    base_addr: usize,
    layout_size: usize,
    layout_align: usize,
    page_size: usize,
    metadata_size: usize,
    initialized: bool
}

impl TrustedBitfield8 {
    const SIZE: usize = 8;  // Change this for other bitfield sizes
    pub fn new(
        for_size: usize,
        capacity: usize,
        base_addr: usize,
        layout_size: usize,
        layout_align: usize,
        page_size: usize,
        metadata_size: usize
    ) -> Option<Self> {
        let valid_args =
            for_size > 0 && capacity > 0 && for_size < capacity &&
            layout_align > 0 && layout_size > 0 &&
            layout_align.is_power_of_two() && layout_size % layout_align == 0;
        if valid_args {
            let bitfield = [0, 0, 0, 0, 0, 0, 0, 0];  // Change this for other bitfield sizes
            let available_bits = bitfield.len() * 64;
            let wanted_bits = capacity / for_size;
            let relevant_bits = if wanted_bits <= available_bits {wanted_bits} else {available_bits};
            let mut trusted_bitfield = TrustedBitfield8 {  // Change this for other bitfield types
                bitfield, relevant_bits, base_addr, layout_size, layout_align, page_size, metadata_size, initialized: false
            };
            trusted_bitfield.initialize();
            Some(trusted_bitfield)
        } else {None}
    }
    pub fn initialize(&mut self) {initialize(&mut self.bitfield, self.relevant_bits)}
    pub fn first_fit(&self) -> Option<(usize, usize)> {first_fit(&self.bitfield, self.base_addr, self.layout_size, self.layout_align, self.page_size, self.metadata_size)}
    pub fn is_allocated(&self, idx: usize) -> Option<bool> {is_allocated(&self.bitfield, idx)}
    pub fn set_bit(&mut self, idx: usize) -> Option<bool> {set_bit(&mut self.bitfield, idx)}
    pub fn clear_bit(&mut self, idx: usize) -> Option<bool> {clear_bit(&mut self.bitfield, idx)}
    pub fn is_full(&self) -> bool {is_full(&self.bitfield)}
    pub fn all_free(&self) -> bool {all_free(&self.bitfield, self.relevant_bits)}
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

// #[requires(bitfield.len() > 0)]
// #[requires(relevant_bits > 0)]
// #[requires(relevant_bits <= bitfield.len() * 64)]
// #[ensures(bitfield.len() == old(bitfield.len()))]
// #[ensures(forall(|i: usize| ((i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0)))]
// #[ensures(forall(|i: usize| (i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==> bitfield[i].trailing_zeros() as usize == relevant_bits % 64)))]
// #[ensures(forall(|i: usize| (i < bitfield.len() && i * 64 >= relevant_bits ==> bitfield[i] == U64_MAX)))]
// fn initialize(bitfield: &mut [u64], relevant_bits: usize) {
//     let mut i: usize = 0;
//     while i < bitfield.len() {

//         body_invariant!(i < bitfield.len());
//         body_invariant!(bitfield.len() == old(bitfield.len()));
//         body_invariant!(i * 64 < relevant_bits ==> forall(|j: usize| j < i ==> bitfield[j] == 0));
//         // body_invariant!(i > 0 && i * 64 == relevant_bits ==> bitfield[i - 1] == 0);
//         body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));
//         body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| (j * 64 >= relevant_bits && j < i ==> bitfield[j] == U64_MAX)));
//         body_invariant!(i * 64 >= relevant_bits ==>
//             forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits && j < i ==>
//                 bitfield[j].trailing_zeros() as usize == relevant_bits % 64
//             ))
//         );
//         // body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| (j * 64 >= relevant_bits && j < i ==> bitfield[j] == U64_MAX)));
//         // body_invariant!((i + 1) * 64 <= relevant_bits)
//         // body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));

//         let bit_idx = i * 64;
//         if bit_idx <= relevant_bits {
//             let remaining_bits = relevant_bits - bit_idx;
//             prusti_assert!(remaining_bits == relevant_bits - bit_idx);
//             prusti_assert!(relevant_bits % 64 == (relevant_bits - bit_idx) % 64);
//             prusti_assert!(relevant_bits % 64 == remaining_bits % 64);
//             prusti_assert!(remaining_bits < 64 ==> relevant_bits % 64 == remaining_bits);
//             if remaining_bits >= 64 {bitfield[i] = 0;}
//             else {
//                 bitfield[i] = make_trailing_zeros_u64(remaining_bits as u32);
//                 prusti_assert!(bitfield[i].trailing_zeros() as usize == remaining_bits);
//                 prusti_assert!(bitfield[i].trailing_zeros() as usize == relevant_bits % 64);
//             }
//         } else {bitfield[i] = U64_MAX;}
        
//         // let remaining_bits_opt = relevant_bits.checked_sub(i * 64);
//         // if let Some(remaining_bits) = remaining_bits_opt {
//         //     // prusti_assert!(remaining_bits == relevant_bits - i * 64);
//         //     // prusti_assert!(relevant_bits % 64 == (relevant_bits - i * 64) % 64);
//         //     // prusti_assert!(relevant_bits % 64 == remaining_bits % 64);
//         //     if remaining_bits >= 64 {bitfield[i] = 0;}
//         //     else {
//         //         prusti_assert!(remaining_bits < 64);
//         //         prusti_assert!(remaining_bits > 0 ==> remaining_bits == relevant_bits % 64);
//         //         prusti_assert!(remaining_bits == 0 ==> relevant_bits == i * 64);
//         //         // prusti_assert!(remaining_bits == 0 ==> relevant_bits % 64 == 0);
//         //         // prusti_assert!(remaining_bits == relevant_bits )
//         //         // prusti_assert!(remaining_bits == relevant_bits % 64);
//         //         bitfield[i] = make_trailing_zeros_u64(remaining_bits as u32);
//         //         // prusti_assert!(bitfield[i].trailing_zeros() as usize == relevant_bits % 64);
//         //     }
//         // } else {bitfield[i] = U64_MAX;}

//         prusti_assert!(i * 64 >= relevant_bits ==> bitfield[i] == U64_MAX);
//         prusti_assert!((i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0);
//         prusti_assert!(i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==>
//             bitfield[i].trailing_zeros() == (relevant_bits - bit_idx) as u32);
//         // prusti_assert!(i * 64 <= relevant_bits && (i + 1) * 64 > relevant_bits ==>
//         //     bitfield[i].trailing_zeros() == peek_option(&remaining_bits_opt) as u32);

//         // prusti_assert!(i * 64 > relevant_bits ==)
//         // prusti_assert!(i * 64 <= relevant_bits && (i + 1) * 64 > relevant_bits ==>
//         //     relevant_bits - bit_idx == relevant_bits % 64);

//         // prusti_assert!((i + 1) * 64 <= relevant_bits ==> forall(|j: usize| j <= i ==> bitfield[j] == 0));
//         // prusti_assert!(i * 64 >= relevant_bits ==> forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));
//         // prusti_assert!((i + 1) * 64 > relevant_bits ==> forall(|j: usize| j <= i ==> bitfield[j] == 0));

//         i += 1;
//     }
//     prusti_assert!(i > 0);
//     prusti_assert!(i == bitfield.len());
//     prusti_assert!(forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));
//     prusti_assert!(forall(|j: usize| (j * 64 >= relevant_bits && j < bitfield.len() ==> bitfield[j] == U64_MAX)));
//     prusti_assert!(
//         forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==>
//             bitfield[j].trailing_zeros() as usize == relevant_bits % 64
//         ))
//     );
//     // prusti_assert!(forall(|j: usize) (i * 64 < relevant_bits ))
//     // prusti_assert!()
//     // prusti_assert!()
//     // prusti_assert!(relevant_bits)
//     // i -= 1;
//     // prusti_assert!(i < bitfield.len() && i * 64 > relevant_bits ==> forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));
//     // prusti_assert!(i )
//     // prusti_assert!(forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> j < bitfield.len())));
//     // prusti_assert!(forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));
//     // prusti_assert!(forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));

// }