use prusti_contracts::*;
use crate::my_layout::Layout;
use crate::external_spec::{trusted_option::*, trusted_num::*};

const U64_MAX: u64 = 18_446_744_073_709_551_615u64;
const U64_POW_63: u64 = 9_223_372_036_854_775_808u64;

// Base cases
#[ensures(n == 0 ==> !result)]
#[ensures(n == 1 ==> result)]
#[ensures(n == 2 ==> result)]

#[ensures(result && n < U64_POW_63 ==>              // Induction hypothesis: if n is a power of 2 then (n * 2) must be as well
            is_power_of_two_u64(n * 2))]            // This applies when n < 2 ^ 63, since that's the maximum possible
                                                    // power of 2.

#[ensures(result ==> n.checked_ilog2().is_some())]  // See assurances for checked_ilog2 above. If n is a
                                                    // power of 2, it must be non-zero. Therefore, its integer log
                                                    // must exist.

#[ensures(result ==> {                              // Since we can take the log of n as seen above, we can also raise 2 to
    let l = n.checked_ilog2();                      // that power without overflow (since the maximum that checked_ilog2
    2u64.checked_pow(peek_option(&l)).is_some()     // returns is 63)
})]

#[ensures(result ==> {                              // If n is a power of 2,
    let l = n.checked_ilog2();                      // we should be able to take the integer log2 of n,
    let p = 2u64.checked_pow(peek_option(&l));      // and raise 2 to the power of that
    peek_option(&p) == n                            // to obtain n again.
})]

// If n is a power of 2, then there are no powers of 2 between n and n * 2 exclusive.
#[ensures(n > U64_POW_63 ==> !result)]
#[ensures(n == U64_POW_63 ==> result)]
#[ensures(result && n < U64_POW_63 ==> forall(
    |i: u64| (n < i && i < n * 2 ==> !is_power_of_two_u64(i))
))]

#[pure]
#[trusted]
fn is_power_of_two_u64(n: u64) -> bool {
    u64::is_power_of_two(n)
}

// #[ensures(n == 0 ==> result)]
// #[ensures(n == 1 ==> result)]
// #[ensures(n == 2 ==> !result)]
// #[ensures(result && n < U64_MAX ==> n < U64_POW_63)]
// #[ensures(result && n < U64_MAX ==> is_power_of_two_u64(n + 1))]
// #[ensures(result && n < U64_POW_63 ==> true //n <= U64_POW_63 / 2
// )]
// #[ensures(result && n < U64_POW_63 ==> u64::is_power_of_two(2 * n + 2))]
// #[ensures(result && n < U64_MAX ==> (2 * n + 1) == U64_MAX || u64::is_power_of_two(2 * (n + 1)))]
// #[ensures(is_power_of_two_u64(n + 1) && n < U64_MAX ==> result)]

// Basic post-conditions
#[ensures(n == 0 ==> result)]
#[ensures(n == 1 ==> result)]
#[ensures(n == U64_MAX ==> result)]
#[ensures(result && n < U64_MAX ==> is_power_of_two_u64(n + 1))]

// Ensures that (2n + 1) is a valid bitfield state if n is.
// Need separate cases for when 2 * n + 1 == U64_MAX and when 2 * n + 1 < U64_MAX
#[ensures(n == U64_POW_63 - 1 ==> 2 * n + 1 == U64_MAX)]
#[ensures(n < U64_POW_63 - 1 ==> 2 * n + 1 < U64_MAX)]
#[ensures(result && n < U64_POW_63 - 1 ==> is_power_of_two_u64(2 * n + 2))]

// Same thing, but with log operations
#[ensures(result && n < U64_POW_63 - 1 ==> is_power_of_two_u64(n + 1))]
#[ensures(result && n < U64_POW_63 - 1 ==> {
    let l = (n + 1).checked_ilog2();
    l.is_some() ==> {
        let p = 2u64.checked_pow(peek_option(&l));
        p.is_some() ==> is_power_of_two_u64(n + peek_option(&p) + 1)
    }
})]

// Ensures that (2n + 1) is the next valid bitfield state if n is
#[ensures(result && n < U64_POW_63 - 1 ==> forall(
    |i: u64| n + 1 < i && i <= 2 * n + 1 ==> !is_power_of_two_u64(i)
))]

#[pure]
pub fn is_bitfield_u64_valid(n: u64) -> bool {
    if n == U64_MAX {true} else {is_power_of_two_u64(n + 1)}
}

// Basic assurances
#[requires(u < U64_MAX)]
#[requires(is_bitfield_u64_valid(u))]
#[requires(is_power_of_two_u64(u + 1))]
#[requires(is_bitfield_u64_valid(2 * u + 1))]

// Sanity check: we can raise 2 to the power of result
#[ensures(2u64.checked_pow(result as u32).is_some())]

// Sanity check: 2 ^ result = n + 1
#[ensures({
    let p = 2u64.checked_pow(result as u32);
    peek_option(&p) == u + 1
})]

// Check that u + 2 ^ result is a valid bitfield
#[ensures(
    {let p = 2u64.checked_pow(result as u32);
    is_bitfield_u64_valid(u + peek_option(&p))}
)]

// Check that u + 2 ^ result == 2 * u + 1 (same as above)
#[ensures(
    {let p = 2u64.checked_pow(result as u32);
    u + peek_option(&p) == 2 * u + 1}
)]
fn first_fit_idx(u: u64) -> u64 {
    match (u + 1).checked_ilog2() {
        Some(r) => r as u64,
        None => unreachable!(),
    }
}

// #[requires(layout.size() > 0)]
// #[requires(layout.align() > 0)]
// fn check_first_fit_overlap_and_alignment(
//     offset: usize,
//     addr: usize,
//     layout: Layout,
//     page_size: usize,
//     metadata_size: usize
// ) -> bool {
//     offset > (page_size - metadata_size - layout.size()) && addr % layout.align() == 0
// }

#[requires(layout.size() > 0)]
#[requires(layout.align() > 0)]
#[requires(u < U64_MAX)]
#[requires(is_bitfield_u64_valid(u))]
pub fn first_fit_in_u64 (
    u: u64,
    base_idx: usize,
    base_addr: usize,
    layout: Layout,
    page_size: usize,
    metadata_size: usize
// ) -> Option<(VerifiedOffset, VerifiedAllocationAddress)> {
) -> Option<(usize, usize)> {
    let first_free = first_fit_idx(u) as usize;
    let idx = base_idx * 64 + first_free;
    let offset = idx * layout.size();
    let addr = base_addr + offset;
    if offset > (page_size - metadata_size - layout.size()) && addr % layout.align() == 0 {
        Some((idx, addr))
    } else {None}

    // if check_first_fit_overlap_and_alignment(offset, addr, layout, page_size, metadata_size) {
    //     Some((idx, addr))
    // } else {
    //     None
    // }
}

// https://stackoverflow.com/questions/600293/how-to-check-if-a-number-is-a-power-of-2
// #[trusted]
// #[pure]
// #[ensures(n == 0 ==> !result)]
// #[ensures(n == 1 ==> result)]
// #[ensures(n == 2 ==> result)]
// #[ensures(n > 1 && n % 2 != 0 ==> !result)]
// // #[ensures(result ==> n <= 1 || n % 2 == 0)]
// // #[ensures(n < 9_223_372_036_854_775_808u64 ==> is_power_of_two_u64(n) == is_power_of_two_u64(n * 2))]
// // #[ensures(n == 9_223_372_036_854_775_808u64 ==> result)]
// // #[ensures(n > 9_223_372_036_854_775_808u64 ==> !result)]
// // #[ensures(n < 9_223_372_036_854_775_808u64 && is_power_of_two_u64(n) ==> n <= 4_611_686_018_427_387_904u64)]
// // #[ensures(n < 9_223_372_036_854_775_808u64 )]
// // #[ensures(n < 9_223_372_036_854_775_808u64 && is_power_of_two_u64(n) ==> n <= )]
// // #[ensures(is_power_of_two_u64(n) ==> n <= U64_POW_63)]
// #[ensures(is_power_of_two_u64(n) ==> is_power_of_two_u64(n * 2))]
// // #[ensures(n < U64_POW_63 && is_power_of_two_u64(n) ==> is_power_of_two_u64(n * 2))]
// fn is_power_of_two_u64(n: u64) -> bool {
//     n != 0 && (n & (n - 1) == 0)
// }

// #[trusted]
// #[pure]
// #[ensures(n == 0 ==> !result)]
// #[ensures(n == 1 ==> result)]
// #[ensures(n == 2 ==> result)]
// #[ensures(n > 1 && n % 2 != 0 ==> !result)]
// #[ensures(result ==> n <= 1 || n % 2 == 0)]
// #[ensures(is_power_of_two_usize(n) ==> is_power_of_two_usize(n * 2))]
// fn is_power_of_two_usize(n: usize) -> bool {
//     n != 0 && (n & (n - 1) == 0)
// }

// #[trusted]
// #[pure]
// #[ensures(p == 0 ==> result == 1)]
// #[ensures(p > 0 ==> result == 2 * power_of_2(p - 1))]
// #[ensures(is_power_of_two_u64(result))]
// fn power_of_2(p: u64) -> u64 {
//     if p == 0 {1} else {2 * power_of_2(p - 1)}
// }

// #[requires(is_power_of_two_u64(acc))]
// // #[requires(acc < 9_223_372_036_854_775_808u64 ==> acc <= 4_611_686_018_427_387_904u64)]
// // #[requires(acc <= 9_223_372_036_854_775_808u64)]
// // #[requires(n > 0 ==> acc <= n)]
// fn log_u64_aux(res: u64, acc: u64, n: u64) -> u64 {
//     if acc == 9_223_372_036_854_775_808u64 || acc == n || acc * 2 > n {
//         res
//     } else {log_u64_aux(res + 1, acc * 2, n)}
// }

// // #[ensures(power_of_2(result) <= n)]
// // Technically constant time, since there is at most 64 recursive calls.
// // Returns 63 at most.
// fn log_u64(n: u64) -> u64 {
//     log_u64_aux(0, 1, n)
// }

// #[trusted]
// #[pure]
// #[ensures(n == 1 ==> result)]
// #[ensures(is_power_of_two_usize(n) ==> is_power_of_two_usize(n * 2))]
// fn is_power_of_two_usize(n: usize) -> bool {
//     if n % 2 != 0 {n == 1} else {is_power_of_two_usize(n / 2)} 
// }

// #[trusted]
// #[pure]
// #[ensures(n == 0 ==> !result)]
// #[ensures(n == 1 ==> result)]
// #[ensures(result ==> is_power_of_two_u64(n * 2))]
// #[ensures(n > 1 && result ==> n % 2 == 0)]
// #[ensures(n > 2 && n % 2 == 0 && (n / 2) % 2 != 0 ==> !result)]
// #[ensures(is_power_of_two_u64(n) == is_power_of_two_u64(n * 2))]
// #[ensures(n > 1 ==> n % 2 == 0)]
// #[ensures(n == 2 ==> result)]
// #[ensures(n == 3 ==> !result)]
// #[ensures(n != 1 n > 1 && n % 2 == 0)]
// #[ensures(result ==> n % 2 == 0)]
// #[ensures(result ==> n <= 9_223_372_036_854_775_808u64)]
// #[ensures(n > 9_223_372_036_854_775_808u64 ==> result == false)] // cp <= 2u64.pow(63)
// #[ensures(n < 9_223_372_036_854_775_808u64 && is_power_of_two_u64(n) ==> is_power_of_two_u64(n * 2))]
// fn is_power_of_two_u64(n: u64) -> bool {
//     if n % 2 != 0 {n == 1} else {is_power_of_two_u64(n / 2)} 
// }

// #[pure]
// #[requires()]
// #[requires(cp * 2 <= 9_223_372_036_854_775_808u64)]
// #[requires(cp <= 9_223_372_036_854_775_808u64)] // cp <= 2u64.pow(63)
// #[requires(exists)]
// #[requires(cp == 1)]
// #[pure]
// #[ensures(cp >= 9_223_372_036_854_775_808u64 ==> result == (n == 0))]
// #[requires(is_power_of_two_u64(cp))]
// #[pure]
// fn is_bitfield_u64_valid_aux(cp: u64, n: u64) -> bool {
//     // if n == 0 {
//     //     true
//     // } else if cp > n {
//     //     false
//     // } else {
//     //     // false
//     //     is_bitfield_u64_valid_aux(cp * 2, n - cp)
//     // }

//     if cp >= 9_223_372_036_854_775_808u64 {
//         n == 0
//     } else {
//         // #[ensures(cp < 9_223_372_036_854_775_808u64)]
//         is_bitfield_u64_valid_aux(cp * 2, n - cp)
//     }

    
//     // if acc == 18_446_744_073_709_551_615u64 {
//     //     true
//     // } 
// }

// #[requires(is_power_of_two_u64(cpow))]
// #[requires(cpow < 9_223_372_036_854_775_808u64 ==> cpow > acc)]
// #[ensures(acc == 0 && n == 0 ==> result)]
// #[ensures(acc == n ==> result)]
// #[ensures(acc + cpow == n ==> result)]
// #[ensures(acc > n ==> !result)]
// #[ensures(acc < n && acc + cpow > n ==> !result)]
// #[ensures(cpow == 2 && acc == 1 && n == 2 ==> !result)]
// #[ensures(cpow == 1 && acc == 0 && n == 2 ==> !result)]
// // #[ensures(acc == 0 && n == 1 ==> result)]
// // #[ensures(acc > n ==> !result)]
// // #[requires(cpow <= 9_223_372_036_854_775_808u64)]
// fn is_bitfield_u64_valid_acc_aux(cpow: u64, acc: u64, n: u64) -> bool {
//     if acc == n { // Case where n == 0 is already covered by the first call where acc == 0.
//         true
//     } else if acc > n {
//         false
//     } else {
//         let ncpow = if cpow == 9_223_372_036_854_775_808u64 {cpow} else {cpow * 2}; // Prevent overflow; stop when cpow == 2 ** 63
//         is_bitfield_u64_valid_acc_aux(ncpow, acc + cpow, n)
//     }
// }

// #[ensures(n == 0 ==> result)]
// #[ensures(n == 1 ==> result)]
// // #[ensures(n > 0 && result ==> n % 2 == 1)]
// #[ensures(n == 2 ==> !result)]
// // #[ensures(n == 3 ==> !result)]
// // #[ensures(n == 18_446_744_073_709_551_615u64 ==> result)]
// fn is_bitfield_u64_valid(n: u64) -> bool {
//     is_bitfield_u64_valid_acc_aux(1, 0, n)
// }

// #[pure]
// fn is_bitfield_u64_valid(n: u64) -> bool {
//     is_bitfield_u64_valid_aux(1, n)
// }

// #[requires(layout.align() > 0)]
// #[requires(layout.size() > 0)]
// #[requires(*u < 18_446_744_073_709_551_615u64)]
// // #[requires(is_bitfield_u64_valid(*u))]
// // #[requires]
// #[requires(metadata_size < page_size)]
// #[requires(base_idx <= page_size / layout.size() - base_addr)]
// fn first_fit(
//     u: &mut u64,
//     base_idx: usize,
//     base_addr: usize, // Should base_addr be a constant field of the TrustedBitfield struct?
//     layout: Layout,
//     page_size: usize,
//     metadata_size: usize // Actually ditto for all arguments here
// ) -> Option<(usize, usize)> {
//     let first_free = trailing_ones(u);
//     let idx: usize = base_idx * 64 + first_free;
//     let offset = idx * layout.size();

//     let offset_inside_data_area = offset <= (page_size - metadata_size - layout.size());
//     if !offset_inside_data_area {
//         return None;
//     }

//     let addr: usize = base_addr + offset;
//     let alignment_ok = addr % layout.align() == 0;
//     if alignment_ok {
//         return Some((idx, addr));
//     }
//     None
// }

// #[requires(*n < 18_446_744_073_709_551_615u64)]
// #[requires(cp < 18_446_744_073_709_551_615u64)]
// // #[requires(acc < 64)]
// fn trailing_ones_aux(cp: u64, acc: usize, n: &u64) -> usize {
//     if cp > *n {
//         acc
//     } else {
//         trailing_ones_aux(cp * 2, acc + 1, n)
//     }
// }

// #[requires(*n < 18_446_744_073_709_551_615u64)]
// fn trailing_ones(n: &u64) -> usize {
//     trailing_ones_aux(1, 0, n)
// }

// fn leading_zeros(cp: u64, n: u64) {
//     if 
// }

// fn first_free(u: u64) -> u64 {
//     let negated = !u;
//     4
//     // (!u).trailing_zeros()
// }

// #[requires(*u < 18_446_744_073_709_551_615u64)] // Must be less than the maximum value of u64
// #[requires(metadata_size < page_size)]
// fn first_fit_in_u64(
//     u: &mut u64,
//     base_addr: usize, // Should base_addr be a constant field of the TrustedBitfield struct?
//     layout: Layout,
//     page_size: usize,
//     metadata_size: usize // Actually ditto for all arguments here
// ) -> Option<(usize, usize)> {
//     Some((5, 5))
// }

// fn first_fit(
//     u: &mut u64,
//     base_addr: usize, // Should base_addr be a constant field of the TrustedBitfield struct?
//     layout: Layout,
//     page_size: usize,
//     metadata_size: usize // Actually ditto for all arguments here
// ) -> Option<(usize, usize)> {

// }

// fn first_fit(
//     &mut u64,
//     base_addr: usize, // Should base_addr be a constant field of the TrustedBitfield struct?
//     layout: Layout,
//     page_size: usize,
//     metadata_size: usize // Actually ditto for all arguments here
// ) -> Option<(usize, usize)> {
//     for (base_idx, b) in self.bitfield.borrow_mut().iter_mut().enumerate() {
//         let bitval = *b; // b.load(Ordering::Relaxed);
//         if bitval == u64::max_value() {
//             continue;
//         } else {
//             let negated = !bitval;
//             let first_free = negated.trailing_zeros() as usize;
//             let idx: usize = base_idx * 64 + first_free;
//             let offset = idx * layout.size();

//             // TODO(bad): psize needs to be passed as arg
//             let offset_inside_data_area = offset <= (page_size - metadata_size - layout.size());
//             if !offset_inside_data_area {
//                 return None;
//             }

//             let addr: usize = base_addr + offset;
//             let alignment_ok = addr % layout.align() == 0;
//             let block_is_free = bitval & (1 << first_free) == 0;
//             if alignment_ok && block_is_free {
//                 // insert range here
//                 if self.idx_list.insert(idx) {
//                     return Some((idx, addr));
//                 }
//             }
//         }
//     }
//     None
// }