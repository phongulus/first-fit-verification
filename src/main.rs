// #![no_std]
mod external_spec;

mod first_impl;
use first_impl::*;

mod second_impl;
use second_impl::*;

mod my_layout;
use my_layout::Layout;

const U64_MAX: u64 = 18_446_744_073_709_551_615u64;

fn main() {
    // println!("{}", u64::max_value() >> 62); // Rust caching bug? try shifting by 64, then 63, then 62, then 63 again.
    
    let base_idx = 5;
    let base_addr = 20;
    let page_size = 6;
    let metadata_size = 5;
    let layout_maybe = Layout::from_size_align(2, 4);
    if let Some(layout) = layout_maybe {
        let u = 7u64;
        if first_impl::is_bitfield_u64_valid(u) && u < U64_MAX {
            let _ = first_impl::first_fit_in_u64(u, base_idx, base_addr, layout, page_size, metadata_size);
        };

        let test_bitfield_opt = second_impl::TrustedBitfield8::new(8, 64, base_addr, layout, page_size, metadata_size);
        match test_bitfield_opt {
            Some(test_bitfield) => test_bitfield.first_fit(),
            None => None,
        };
        // assert!(test_bitfield_opt);
        // let test_bitfield = test_bitfield_opt.unwrap();
        // let _ = test_bitfield.first_fit();
        // let _ = second_impl::first_fit_in_u64(u, base_idx, base_addr, layout, page_size, metadata_size);
    }
}
