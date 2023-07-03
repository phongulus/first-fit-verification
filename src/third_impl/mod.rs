use prusti_contracts::*;
use crate::my_layout::Layout;
use crate::external_spec::{trusted_option::*};
use core::cell::RefCell;

const U64_MAX: u64 = 18_446_744_073_709_551_615u64;


// Basic bitfield operations with properties verified externally with Verus.

#[pure]
#[trusted]
#[requires(k < 64)]
#[ensures(k == 0 ==> result == 1)]
#[ensures(result > 0)]  // This is the case when k < 64, as the single 1 cannot be shifted out.
#[ensures(result < U64_MAX)]  // Follows from U64_MAX being a sum of unique powers of 2
fn power_of_two_u64(k: usize) -> u64 {
    1 << (k as u64)
}

#[pure]
#[trusted]
#[requires(idx < 64)]
#[ensures(forall(|i: usize| i < 64 && is_allocated_u64(u, i) ==> *u == U64_MAX))] // Need to prove
// #[ensures(!result ==> *u <= U64_MAX - power_of_two_u64(idx))]
// #[ensures(!result ==> *u < U64_MAX)]
// #[ensures(*u == U64_MAX ==> result)]
fn is_allocated_u64(u: &u64, idx: usize) -> bool {
    *u & (1 << idx) > 0
}

#[trusted]
#[requires(idx < 64)]
#[ensures({  // If the bit is previously set, there should be no change to u.
    is_allocated_u64(old(u), idx) <==> old(*u) == *u
})]
#[ensures({  // If the bit is not set, u should be changed to u + 2^idx.
    let p = power_of_two_u64(idx);
    !is_allocated_u64(old(u), idx) ==> old(*u) + p == *u
})]
#[ensures(is_allocated_u64(u, idx))]  // Regardless of whether u is updated or not, the bit should be 1 when the function returns.
fn set_bit_u64(u: &mut u64, idx: usize) {
    *u = *u | (1 << idx);
}

#[trusted]
#[requires(idx < 64)]
#[ensures({  // If the bit is previously cleared, there should be no change to u.
    !is_allocated_u64(old(u), idx) ==> old(*u) == *u
})]
#[ensures({  // If the bit is set, u should be changed to u - 2^idx.
    let p = power_of_two_u64(idx);
    is_allocated_u64(old(u), idx) ==> old(*u) - p == *u
})]
#[ensures(!is_allocated_u64(u, idx))]  // Regardless of whether u is updated or not, the bit should be 0 when the function returns.
fn clear_bit_u64(u: &mut u64, idx: usize) {
    *u = *u & !(1 << idx);
}

#[pure]
#[trusted]
#[requires(k <= 64)]
#[ensures(k == 0 ==> result == U64_MAX)]
#[ensures(k == 64 ==> result == 0)]
#[ensures(forall(|j: usize| j < k ==> !is_allocated_u64(&result, j)))]
#[ensures(forall(|j: usize| j >= k && j < 64 ==> is_allocated_u64(&result, j)))]
fn make_trailing_zeros_u64(k: usize) -> u64 {
    if k == 64 {0}
    else {U64_MAX << k}
}

#[pure]
#[trusted]
#[requires(k <= 64)]
#[ensures(k == 0 ==> result == 0)]
#[ensures(k == 64 ==> result == U64_MAX)]
#[ensures(forall(|j: usize| j < k ==> is_allocated_u64(&result, j)))]
#[ensures(forall(|j: usize| j >= k && j < 64 ==> !is_allocated_u64(&result, j)))]
fn make_trailing_ones_u64(k: usize) -> u64 {
    !make_trailing_zeros_u64(k)
}

#[ensures(result <= 64)]
#[ensures(*u < U64_MAX ==> result < 64)]
#[ensures(forall(|k: usize| k < result ==> is_allocated_u64(u, k)))]
fn my_trailing_ones(u: &u64) -> usize {
    let mut k = 0;
    while k < 64 {
        body_invariant!(k < 64);
        body_invariant!(forall(|j: usize| j < k ==> is_allocated_u64(u, j)));
        if !is_allocated_u64(u, k) {
            prusti_assert!(k < 64);
            // prusti_assert!(*u < U64_MAX);
            break;
        }
        prusti_assert!(is_allocated_u64(u, k));
        prusti_assert!(forall(|j: usize| j <= k ==> is_allocated_u64(u, j)));
        prusti_assert!(k == 63 ==> forall(|j: usize| j < 64 ==> is_allocated_u64(u, j)));
        k += 1
    };
    prusti_assert!(k == 64 ==> *u == U64_MAX);
    // prusti_assert!(*u == U64_MAX ==> k == 64);
    // prusti_assert!(k < 64 <==> *u < U64_MAX);
    k
}

#[ensures(result <= 64)]
#[ensures(forall(|k: usize| k < result ==> !is_allocated_u64(u, k)))]
fn my_trailing_zeros(u: &u64) -> usize {
    let mut k = 0;
    while k < 64 {
        body_invariant!(k < 64);
        body_invariant!(forall(|j: usize| j < k ==> !is_allocated_u64(u, j)));
        if is_allocated_u64(u, k) {break;}
        prusti_assert!(!is_allocated_u64(u, k));
        k += 1
    }; k
}

#[requires(bitfield.len() > 0)]
#[requires(relevant_bits > 0)]
#[requires(relevant_bits <= bitfield.len() * 64)]  // Relevant bits within array bounds.
#[ensures(bitfield.len() == old(bitfield.len()))]  // No change to the length of the u64 array.
#[ensures(forall(|i: usize| ((i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0)))]  // All relevant bits in u64's before the one containing the final relevant bit must be set to 0.
#[ensures(forall(|i: usize| (i < bitfield.len() && i * 64 >= relevant_bits ==> bitfield[i] == U64_MAX)))] // All bits after the u64 containing the final relevant bit must be set to allocated.
#[ensures(forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==>  // The u64 containing the final relevant bit is set correctly.
    forall(|k: usize| (k < relevant_bits - j * 64 ==> !is_allocated_u64(&bitfield[j], k)))
)))]
#[ensures(forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
    forall(|k: usize| (k >= relevant_bits - j * 64 && k < 64 ==> is_allocated_u64(&bitfield[j], k)))
)))]
fn initialize(bitfield: &mut [u64], relevant_bits: usize) {
    let mut i: usize = 0;
    while i < bitfield.len() {

        body_invariant!(i < bitfield.len());
        body_invariant!(bitfield.len() == old(bitfield.len()));
        body_invariant!(i * 64 < relevant_bits ==> forall(|j: usize| j < i ==> bitfield[j] == 0));
        body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));
        body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| (j * 64 >= relevant_bits && j < i ==> bitfield[j] == U64_MAX)));
        body_invariant!(i * 64 >= relevant_bits ==> 
            forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
                forall(|k: usize| k < (relevant_bits - j * 64) ==> !is_allocated_u64(&bitfield[j], k))    
            ))
        );
        body_invariant!(i * 64 >= relevant_bits ==> 
            forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
                forall(|k: usize| k >= (relevant_bits - j * 64) && k < 64 ==> is_allocated_u64(&bitfield[j], k))    
            ))
        );

        let bit_idx = i * 64;
        if bit_idx <= relevant_bits {
            let remaining_bits = relevant_bits - bit_idx;
            if remaining_bits >= 64 {bitfield[i] = 0;}
            else {
                bitfield[i] = make_trailing_zeros_u64(remaining_bits);
                prusti_assert!(forall(|j: usize| j < remaining_bits ==> !is_allocated_u64(&bitfield[i], j)));
                prusti_assert!(forall(|j: usize| (j >= remaining_bits && j < 64) ==> is_allocated_u64(&bitfield[i], j)));
            }
        } else {bitfield[i] = U64_MAX;}

        prusti_assert!(i * 64 >= relevant_bits ==> bitfield[i] == U64_MAX);
        prusti_assert!((i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0);
        prusti_assert!(i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==>
            forall(|j: usize| j < relevant_bits - bit_idx ==> !is_allocated_u64(&bitfield[i], j)));
        prusti_assert!(i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==>
            forall(|j: usize| j >= relevant_bits - bit_idx && j < 64 ==> is_allocated_u64(&bitfield[i], j)));

        i += 1;
    }
    prusti_assert!(i > 0);
    prusti_assert!(i == bitfield.len());
    prusti_assert!(forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));
    prusti_assert!(forall(|j: usize| (j * 64 >= relevant_bits && j < bitfield.len() ==> bitfield[j] == U64_MAX)));
    prusti_assert!(forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
        forall(|k: usize| (k < relevant_bits - j * 64 ==> !is_allocated_u64(&bitfield[j], k)))
    )));
    prusti_assert!(forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
        forall(|k: usize| (k >= relevant_bits - j * 64 && k < 64 ==> is_allocated_u64(&bitfield[j], k)))
    )));
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
#[ensures(result ==> forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==>
    forall(|k: usize| (k < relevant_bits - j * 64 ==> !is_allocated_u64(&bitfield[j], k)))
)))]
fn all_free(bitfield: &[u64], relevant_bits: usize) -> bool {
    let mut i = 0;
    while i < bitfield.len() {

        body_invariant!(i < bitfield.len());
        body_invariant!(bitfield.len() == old(bitfield.len()));
        body_invariant!(i * 64 <= relevant_bits ==> forall(|j: usize| (j < i ==> bitfield[j] == 0)));
        body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));
        body_invariant!(i * 64 >= relevant_bits ==> 
            forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
                forall(|k: usize| k < (relevant_bits - j * 64) ==> !is_allocated_u64(&bitfield[j], k))    
            ))
        );
        // body_invariant!(i * 64 >= relevant_bits ==> 
        //     forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
        //         forall(|k: usize| k >= (relevant_bits - j * 64) && k < 64 ==> is_allocated_u64(&bitfield[j], k))    
        //     ))
        // );

        let bit_idx = i * 64;
        if bit_idx <= relevant_bits {
            let remaining_bits = relevant_bits - bit_idx;
            if remaining_bits >= 64 {if bitfield[i] != 0 {return false;}}
            else if my_trailing_zeros(&bitfield[i]) != remaining_bits {return false;}
            else {
                prusti_assert!(forall(|j: usize| j < remaining_bits ==> !is_allocated_u64(&bitfield[i], j)));
            }
        } else {}

        // prusti_assert!(i * 64 >= relevant_bits ==> bitfield[i] == U64_MAX);  // Verify that bits outside of relevant_bits are not modified?
        prusti_assert!((i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0);
        prusti_assert!(i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==>
            forall(|j: usize| j < relevant_bits - bit_idx ==> !is_allocated_u64(&bitfield[i], j)));
        // prusti_assert!(i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==>
        //     forall(|j: usize| j >= relevant_bits - bit_idx && j < 64 ==> is_allocated_u64(&bitfield[i], j)));

        i += 1;
    }
    prusti_assert!(i > 0);
    prusti_assert!(i == bitfield.len());
    prusti_assert!(forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == 0)));
    prusti_assert!(forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
        forall(|k: usize| (k < relevant_bits - j * 64 ==> !is_allocated_u64(&bitfield[j], k)))
    )));

    true
}

#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the bitfield isn't changed if the bit
    let base_idx = idx / 64;               // is already 0.
    let bit_idx = idx % 64;
    !is_allocated_u64(old(&bitfield[base_idx]), bit_idx) ==> bitfield[base_idx] == old(bitfield[base_idx])
})]
#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the bitfield value decreased if the bit
    let base_idx = idx / 64;               // was previously set to 1.
    let bit_idx = idx % 64;
    is_allocated_u64(old(&bitfield[base_idx]), bit_idx) ==> bitfield[base_idx] < old(bitfield[base_idx])
})]
#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the correct bit was flipped.
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let p = power_of_two_u64(bit_idx);
    is_allocated_u64(old(&bitfield[base_idx]), bit_idx) ==> old(bitfield[base_idx]) - bitfield[base_idx] == p
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
    is_allocated_u64(old(&bitfield[base_idx]), bit_idx) ==> bitfield[base_idx] == old(bitfield[base_idx])
})]
#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the bitfield value increased if the bit
    let base_idx = idx / 64;               // wasn't previously set.
    let bit_idx = idx % 64;
    !is_allocated_u64(old(&bitfield[base_idx]), bit_idx) ==> bitfield[base_idx] > old(bitfield[base_idx])
})]
#[ensures(idx < bitfield.len() * 64 ==> {  // Check that the correct bit was flipped.
    let base_idx = idx / 64;
    let bit_idx = idx % 64;
    let p = power_of_two_u64(bit_idx);
    !is_allocated_u64(old(&bitfield[base_idx]), bit_idx) ==> bitfield[base_idx] - old(bitfield[base_idx]) == p
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
#[ensures(!is_allocated_u64(&u, result))] // Check that the result index is availble
#[ensures(forall(|j: usize| j < result ==> is_allocated_u64(&u, j)))]  // Check that the result index is the first one available (all previous indices allocated)
fn first_fit_idx(u: u64) -> usize {
    let i = my_trailing_ones(&u);
    prusti_assert!(forall(|j: usize| j < i ==> is_allocated_u64(&u, j)));
    i
}

#[requires(layout.size() > 0)]
#[requires(layout.align() > 0)]
#[requires(u < U64_MAX)]
#[ensures(result.is_some() ==> {  // The returned index should within the bounds of the current u64.
    let (idx, addr) = peek_option(&result);
    idx >= base_idx * 64 && idx < base_idx * 64 + 64
})]
#[ensures(result.is_some() ==> {  // The index is mapped to the correct address.
    let (idx, addr) = peek_option(&result);
    addr == base_addr + idx * layout.size()
})]
#[ensures(result.is_some() ==> {  // Check that the returned address does not overlap with metadata. 
    let (idx, addr) = peek_option(&result);
    addr - base_addr <= page_size - metadata_size - layout.size() && addr % layout.align() == 0
})]
fn first_fit_in_u64 (
    u: u64,
    base_idx: usize,
    base_addr: usize,
    layout: Layout,
    page_size: usize,
    metadata_size: usize
) -> Option<(usize, usize)> {
    let first_free = first_fit_idx(u);
    let idx = base_idx * 64 + first_free;
    let offset = idx * layout.size();
    let addr = base_addr + offset;
    if offset <= (page_size - metadata_size - layout.size()) && addr % layout.align() == 0 {
        Some((idx, addr))
    } else {None}
}

#[requires(layout.size() > 0)]
#[requires(layout.align() > 0)]
#[ensures(result.is_some() ==> {  // Check that the returned index is within range and that the address is correct.
    let (idx, addr) = peek_option(&result);
    idx < bitfield.len() * 64 && addr == base_addr + idx * layout.size()
})]
#[ensures(result.is_some() ==> {  // Check that the returned address does not overlap with metadata.
    let (idx, addr) = peek_option(&result);
    addr - base_addr <= page_size - metadata_size - layout.size() && addr % layout.align() == 0
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
    layout: Layout,
    page_size: usize,
    metadata_size: usize
) -> Option<(usize, usize)> {
    let mut base_idx = 0;
    while base_idx < bitfield.len() {

        body_invariant!(base_idx < bitfield.len());
        body_invariant!(forall(|i: usize| i < base_idx ==> bitfield[i] == U64_MAX));  // All previous u64 must have max value

        if bitfield[base_idx] < U64_MAX {
            return first_fit_in_u64(bitfield[base_idx], base_idx, base_addr, layout, page_size, metadata_size)
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
// #[invariant(self.initialized ==> forall(|i: usize| i < self.bitfield.len() && i * 64 >= self.relevant_bits ==> self.bitfield[i] == U64_MAX))]
pub struct TrustedBitfield8 {  // Change name for other bitfield types
    bitfield: [u64; TrustedBitfield8::SIZE],  // Change name for other bitfield sizes
    relevant_bits: usize,
    base_addr: usize,
    layout: Layout,
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
        layout: Layout,
        page_size: usize,
        metadata_size: usize
    ) -> Option<Self> {
        if for_size > 0 && capacity > 0 && for_size < capacity {
            let bitfield = [0, 0, 0, 0, 0, 0, 0, 0];  // Change this for other bitfield sizes
            let available_bits = bitfield.len() * 64;
            let wanted_bits = capacity / for_size;
            let relevant_bits = if wanted_bits <= available_bits {wanted_bits} else {available_bits};
            let mut trusted_bitfield = TrustedBitfield8 {  // Change this for other bitfield types
                bitfield, relevant_bits, base_addr, layout, page_size, metadata_size, initialized: false
            };
            trusted_bitfield.initialize();
            Some(trusted_bitfield)
        } else {None}
    }
    pub fn initialize(&mut self) {
        let bitfield_ref = &mut self.bitfield;
        let () = initialize(bitfield_ref, self.relevant_bits);
        // prusti_assert!(self.bitfield.len() == old(self.bitfield.len()));
        // The below does not pass?
        // prusti_assert!(forall(|i: usize| ((i + 1) * 64 <= self.relevant_bits ==> self.bitfield[i] == 0)));
        // prusti_assert!(forall(|i: usize| (i * 64 < self.relevant_bits && (i + 1) * 64 > self.relevant_bits ==> self.bitfield[i].trailing_zeros() as usize == self.relevant_bits % 64)));
        // prusti_assert!(forall(|i: usize| (i < self.bitfield.len() && i * 64 >= self.relevant_bits ==> self.bitfield[i] == U64_MAX)));
        self.initialized = true;
    }
    pub fn first_fit(&self) -> Option<(usize, usize)> {first_fit(&self.bitfield, self.base_addr, self.layout, self.page_size, self.metadata_size)}
    pub fn is_allocated(&self, idx: usize) -> Option<bool> {is_allocated(&self.bitfield, idx)}
    pub fn set_bit(&mut self, idx: usize) -> Option<bool> {set_bit(&mut self.bitfield, idx)}
    pub fn clear_bit(&mut self, idx: usize) -> Option<bool> {clear_bit(&mut self.bitfield, idx)}
    pub fn is_full(&self) -> bool {is_full(&self.bitfield)}
    pub fn all_free(&self) -> bool {all_free(&self.bitfield, self.relevant_bits)}
}