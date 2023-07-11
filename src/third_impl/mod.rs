use std::sync::atomic::Ordering;

use prusti_contracts::*;
use crate::my_layout::Layout;

#[allow(unused_imports)]
use crate::external_spec::{trusted_option::*};

const U64_MAX: u64 = 18_446_744_073_709_551_615u64;

// #[derive(Clone, Copy)]
// pub struct AtomicU64(u64);

// #[trusted]
// #[pure]
// #[requires(index < s.len())]
// #[ensures(result == s[index])]
// // #[after_expiry(s.len() == old(s.len()))]
// fn index<T: Copy>(s: &[T], index: usize) -> T {
//     s[index].clone()
// }

// impl AtomicU64 {
//     #[pure]
//     #[trusted]
//     fn load(&self, _order: Ordering) -> u64 {
//         self.0
//     }

//     #[trusted]
//     #[ensures(self.load(_order) == val)]
//     #[ensures(self.0 == val)]
//     // #[assert_on_expiry(true ,self.load(_order) == val)]
//     fn store(&self, val: u64, _order: Ordering) {
//         // unsafe(*self).0 = val;
//     }
// }

// #[trusted]
// #[requires(index < s.len())]
// #[assert_on_expiry(true, s.len() == old(s.len())
//     && forall (|i: usize| i < s.len() && i != index ==> s[i].load(_order) == old(s[i].load(_order)))
//     // && s[index].load(_order) == index_AtomicU64(s, index, _order).load(_order)
// )]
// // #[after_expiry(s[index].load(_order) == index_AtomicU64(s, index, _order).load(_order))]
// fn index_mut_AtomicU64(s: &mut [AtomicU64], index: usize, _order: Ordering) -> &mut AtomicU64 {
//     &mut s[index]
// }

// #[pure]
// #[trusted]
// #[requires(index < s.len())]
// // #[after_expiry(s.len() == old(s.len()))]
// #[ensures(result.load(_order) == s[index].load(_order))]
// fn index_AtomicU64(s: &[AtomicU64], index: usize, _order: Ordering) -> &AtomicU64 {
//     &s[index]
// }

// impl AtomicU64WrapperTrait for AtomicU64Model {
//     #[pure]
//     fn load(&self, _order: Ordering) -> u64 {
//         self.0
//     }

//     fn store(&mut self, val: u64, _order: Ordering) {
//         self.0 = val;
//     }
// }

// #[ensures(a.load(order) == val)]
// fn store_test(a: &mut AtomicU64, val: u64, order: Ordering) {
//     a.store(val, order);
//     prusti_assert!(a.load(order) == val);
// }

// #[requires(a.len() > 0)]
// #[requires(index < a.len())]
// #[ensures(a[index].load(order) == val)]
// #[assert_on_expiry(true, a[index].load(order) == val)]
// #[ensures({
//     let u = index(a, i);
//     u.load(order) == val
// })]
// fn store_test2(a: &mut [AtomicU64], index: usize, val: u64, order: Ordering) {
//     let au64 = index_mut_AtomicU64(a, index, order);
//     au64.store(val, order);
//     prusti_assert!(a.len() == old(a.len()));
//     prusti_assert!(forall (|i: usize| i < a.len() && i != index ==> a[i].load(order) == old(a[i].load(order))));
//     // && s[index].load(_order) == index_AtomicU64(s, index, _order).load(_order)
//     // prusti_assert!(index_AtomicU64(a, i, order).load(order) == a[i].load(order));
//     // let u = index_mut(a, i);
//     // u.store(val, order);
//     // prusti_assert!(u.load(order) == val);
//     // prusti_assert!(index(a, i).load(order) == u.load(order));
//     // prusti_assert!(u.load(order) == a[i].load(order));
//     // prusti_assert!(a[i].load(order) == val);
//     // a[i].store(val, order);
// }


// #[requires(a.len() > 0)]
// #[requires(i < a.len())]
// #[ensures({
//     let u = &a[i];
//     u.load(order) == val
// })]
// fn store_test_2(a: &mut [impl AtomicU64WrapperTrait], i: usize, val: u64, order: Ordering) {
//     a[i].store(val, order)
//     // let u = &mut a[i];
//     // u.store(val, order);
//     // prusti_assert!(u.load(order) == val);
// }

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
#[ensures(forall(|i: usize| i < 64 ==> is_allocated_u64(u, i)) ==> *u == U64_MAX)]  // If all bits are set, u should be U64_MAX.
#[ensures(!result ==> *u < U64_MAX)]  // If any bit is not set, u should be less than U64_MAX.
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
#[ensures(k == 0 ==> result == U64_MAX)]  // If k == 0, all bits should be set.
#[ensures(k == 64 ==> result == 0)]       // If k == 64, all bits should be cleared.
#[ensures(forall(|j: usize| j < k ==> !is_allocated_u64(&result, j)))]  // All bits before the kth bit should be cleared.
#[ensures(forall(|j: usize| j >= k && j < 64 ==> is_allocated_u64(&result, j)))]  // All bits including and after the kth bit should be set.
fn make_trailing_zeros_u64(k: usize) -> u64 {
    if k == 64 {0}
    else {U64_MAX << k}
}

#[pure]
#[trusted]
#[requires(k <= 64)]
#[ensures(k == 0 ==> result == 0)]  // If k == 0, all bits should be cleared.
#[ensures(k == 64 ==> result == U64_MAX)]  // If k == 64, all bits should be set.
#[ensures(forall(|j: usize| j < k ==> is_allocated_u64(&result, j)))]  // All bits before the kth bit should be set.
#[ensures(forall(|j: usize| j >= k && j < 64 ==> !is_allocated_u64(&result, j)))]  // All bits including and after the kth bit should be cleared.
fn make_trailing_ones_u64(k: usize) -> u64 {
    !make_trailing_zeros_u64(k)
}

#[ensures(result <= 64)]  // The result should be within the range of the u64.
#[ensures(*u < U64_MAX ==> result < 64)]  // If u is not U64_MAX, the result should be less than 64.
#[ensures(forall(|k: usize| k < result ==> is_allocated_u64(u, k)))]  // All bits before the result should be set.
#[ensures(result < 64 ==> !is_allocated_u64(u, result))]  // The bit at the result position should be cleared.
fn my_trailing_ones(u: &u64) -> usize {
    let mut k = 0;
    while k < 64 {
        body_invariant!(k < 64);
        body_invariant!(forall(|j: usize| j < k ==> is_allocated_u64(u, j)));
        if !is_allocated_u64(u, k) {
            prusti_assert!(k < 64);
            prusti_assert!(*u < U64_MAX);
            break;
        }
        prusti_assert!(is_allocated_u64(u, k));
        prusti_assert!(forall(|j: usize| j <= k ==> is_allocated_u64(u, j)));
        prusti_assert!(k == 63 ==> forall(|j: usize| j < 64 ==> is_allocated_u64(u, j)));
        k += 1
    };
    prusti_assert!(k == 64 ==> *u == U64_MAX);
    prusti_assert!(k < 64 ==> !is_allocated_u64(u, k));
    k
}

#[ensures(result <= 64)]  // The result should be within the range of the u64.
#[ensures(forall(|k: usize| k < result ==> !is_allocated_u64(u, k)))]  // All bits before the result should be cleared.
#[ensures(result < 64 ==> is_allocated_u64(u, result))]  // The bit at the result position should be cleared.
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
#[ensures(result.is_some() ==> peek_option(&result) ==> is_allocated_u64(&bitfield[idx / 64], idx % 64))]
fn is_allocated(bitfield: &[u64], idx: usize) -> Option<bool> {
    if idx < bitfield.len() * 64 {
        Some(is_allocated_u64(&bitfield[idx / 64], idx % 64))
    } else {None}
}

#[requires(bitfield.len() > 0)]
#[requires(relevant_bits <= bitfield.len() * 64)]
#[requires(relevant_bits > 0)]
#[ensures(!result ==> exists(|i: usize| (  // If the bitfield is not full, there must be at least one bit within the relevant_bits range that is not set.
    ((i + 1) * 64 <= relevant_bits && bitfield[i] < U64_MAX) ||
    (i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits &&
        exists(|j: usize| j < relevant_bits - i * 64 ==> !is_allocated_u64(&bitfield[i], j)))
)))]
#[ensures(result ==> forall(|i: usize| ((i + 1) * 64 <= relevant_bits ==> bitfield[i] == U64_MAX)))]  // If the bitfield is full, all u64's before the one containing the last relevant bit must be set to U64_MAX.
#[ensures(result ==> forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==>  // If the bitfield is full, the u64 containing the last relevant bit must be set correctly (all bits before the last relevant bit are set to 1).
    forall(|k: usize| (k < relevant_bits - j * 64 ==> is_allocated_u64(&bitfield[j], k)))
)))]
fn is_full(bitfield: &[u64], relevant_bits: usize) -> bool {
    let mut i = 0;
    while i < bitfield.len() {

        body_invariant!(i < bitfield.len());
        body_invariant!(i * 64 < relevant_bits ==> forall(|j: usize| j < i ==> bitfield[j] == U64_MAX));
        body_invariant!(i * 64 >= relevant_bits ==> forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == U64_MAX)));
        body_invariant!(i * 64 >= relevant_bits ==> 
            forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
                forall(|k: usize| k < (relevant_bits - j * 64) ==> is_allocated_u64(&bitfield[j], k))    
            ))
        );
        
        let bit_idx = i * 64;
        if bit_idx <= relevant_bits {
            let remaining_bits = relevant_bits - bit_idx;
            if remaining_bits >= 64 {if bitfield[i] != U64_MAX {return false;}}
            else if my_trailing_ones(&bitfield[i]) < remaining_bits {return false;}
            else {
                prusti_assert!(forall(|j: usize| j < remaining_bits ==> is_allocated_u64(&bitfield[i], j)));
            }
        } else {}

        prusti_assert!((i + 1) * 64 <= relevant_bits ==> bitfield[i] == U64_MAX);
        prusti_assert!(i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==>
            forall(|j: usize| j < relevant_bits - bit_idx ==> is_allocated_u64(&bitfield[i], j)));
        
        i += 1;
    }
    prusti_assert!(i > 0);
    prusti_assert!(i == bitfield.len());
    prusti_assert!(forall(|j: usize| ((j + 1) * 64 <= relevant_bits ==> bitfield[j] == U64_MAX)));
    prusti_assert!(forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==> 
        forall(|k: usize| (k < relevant_bits - j * 64 ==> is_allocated_u64(&bitfield[j], k)))
    )));

    true
}

#[requires(bitfield.len() > 0)]
#[requires(relevant_bits <= bitfield.len() * 64)]
#[requires(relevant_bits > 0)]
#[ensures(!result ==> exists(|i: usize| (  // If the bitfield is not empty, there must be at least one bit within the relevant_bits range that is set.
    ((i + 1) * 64 <= relevant_bits && bitfield[i] > 0) ||
    (i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits &&
        exists(|j: usize| j < relevant_bits - i * 64 ==> is_allocated_u64(&bitfield[i], j)))
)))]
#[ensures(result ==> forall(|i: usize| ((i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0)))]  // If the bitfield is empty, all u64's before the one containing the last relevant bit must be set to 0.
#[ensures(result ==> forall(|j: usize| (j * 64 < relevant_bits && (j + 1) * 64 > relevant_bits ==>  // If the bitfield is empty, the u64 containing the last relevant bit must be set correctly (all bits before the last relevant bit are set to 0).
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

        let bit_idx = i * 64;
        if bit_idx <= relevant_bits {
            let remaining_bits = relevant_bits - bit_idx;
            if remaining_bits >= 64 {if bitfield[i] != 0 {return false;}}
            else {
                let tz = my_trailing_zeros(&bitfield[i]);
                if tz < remaining_bits {
                    prusti_assert!(tz < 64);
                    prusti_assert!(is_allocated_u64(&bitfield[i], tz));
                    prusti_assert!(exists(|j: usize| j < remaining_bits && is_allocated_u64(&bitfield[i], j)));
                    return false;
                }
                else {
                    prusti_assert!(forall(|j: usize| j < tz ==> !is_allocated_u64(&bitfield[i], j)));
                    prusti_assert!(remaining_bits <= tz);
                    prusti_assert!(forall(|j: usize| j < remaining_bits ==> !is_allocated_u64(&bitfield[i], j)));
                }
            }
        } else {}

        prusti_assert!((i + 1) * 64 <= relevant_bits ==> bitfield[i] == 0);
        prusti_assert!(i * 64 < relevant_bits && (i + 1) * 64 > relevant_bits ==>
            forall(|j: usize| j < relevant_bits - bit_idx ==> !is_allocated_u64(&bitfield[i], j)));

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
#[ensures(!is_allocated_u64(&u, result))] // Check that the result index is available
#[ensures(forall(|j: usize| j < result ==> is_allocated_u64(&u, j)))]  // Check that the result index is the first one available (all previous indices allocated)
fn first_fit_idx(u: u64) -> usize {
    let i = my_trailing_ones(&u);
    prusti_assert!(i < 64);
    prusti_assert!(!is_allocated_u64(&u, i));
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
pub struct TrustedBitfield8 {  // Change name for other bitfield types
    bitfield: [u64; TrustedBitfield8::SIZE],  // Change name for other bitfield sizes
    relevant_bits: usize,
    base_addr: usize,
    layout: Layout,
    page_size: usize,
    metadata_size: usize
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
                bitfield, relevant_bits, base_addr, layout, page_size, metadata_size
            };
            trusted_bitfield.initialize();
            Some(trusted_bitfield)
        } else {None}
    }
    pub fn initialize(&mut self) {initialize(&mut self.bitfield, self.relevant_bits)}
    pub fn first_fit(&self) -> Option<(usize, usize)> {first_fit(&self.bitfield, self.base_addr, self.layout, self.page_size, self.metadata_size)}
    pub fn is_allocated(&self, idx: usize) -> Option<bool> {is_allocated(&self.bitfield, idx)}
    pub fn set_bit(&mut self, idx: usize) -> Option<bool> {set_bit(&mut self.bitfield, idx)}
    pub fn clear_bit(&mut self, idx: usize) -> Option<bool> {clear_bit(&mut self.bitfield, idx)}
    pub fn is_full(&self) -> bool {is_full(&self.bitfield, self.relevant_bits)}
    pub fn all_free(&self) -> bool {all_free(&self.bitfield, self.relevant_bits)}
}