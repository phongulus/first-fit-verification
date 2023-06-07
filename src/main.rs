// #![no_std]
mod external_spec;

mod first_impl;
use first_impl::*;

mod my_layout;
use my_layout::Layout;

const U64_MAX: u64 = 18_446_744_073_709_551_615u64;

fn main() {
    // println!("{}", u64::max_value() >> 62); // Rust caching bug? try shifting by 64, then 63, then 62, then 63 again.
    
    let layout_maybe = Layout::from_size_align(2, 4);
    if let Some(layout) = layout_maybe {
        let u = 7u64;
        if is_bitfield_u64_valid(u) && u < U64_MAX {
            let _ = first_fit_in_u64(u, 5, 20, layout, 6, 5);
        };
    }
}
