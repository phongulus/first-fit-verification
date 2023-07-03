use vstd::prelude::*;

// Verify with:
// ../verus/source/tools/rust-verify.sh ./src/third_impl/verus_verified.rs --profile

verus! {

    fn main() {

        // Basic assertions on bitshifting by one position.
        assert(forall|i: u64| i >> 1u64 == i / 2) by (bit_vector);
        assert(forall|i: u64| i << 1u64 == mul(i, 2)) by (bit_vector);

        // Equivalence of bit shifting 1u64 with power of 2 function
        // We work with the following specification for the power of 2 function:
        //   - f(0) = 1
        //   - f(n) = 2 * f(n - 1) where n > 0 and n < 64 (due to the limitation of the u64 type)
        // We assume this specification is satisfied by ONE unique function, hence the
        // equivalence between the bitshift expression and the power of 2 function.
        // (Do we need to formally prove the uniqueness of this function?)
        assert(1u64 << 0u64 == 1u64) by (bit_vector);  // Base case
        assert(forall|i: u64| i > 0 && i < 64 ==>
            1u64 << i == mul(2, (1u64 << (sub(i, 1u64))))) by (bit_vector);  // Induction hypothesis

        // From now, we consider the expression (1u64 << k) to be equivalent to 2u64.pow(k)
        // given the above proof.

        // Set bit function properties
        // If the bit was previously set, setting the bit does NOT change anything.
        assert(forall|i: u64, k: u64| #![auto] k < 64 ==> (i & (1u64 << k) > 0 <==> i | (1u64 << k) == i)) by (bit_vector);
        // If the bit was not previously set, setting the bit adds 2^k.
        assert(forall|i: u64, k: u64| #![auto] k < 64 ==> (i & (1u64 << k) == 0 <==> i | (1u64 << k) == add(i, 1u64 << k))) by (bit_vector);
        // Setting the bit, whether changing anything or not, always results in the bit reading 1 afterwards.
        assert(forall|i: u64, k: u64| #![auto] k < 64 ==> ((i | (1u64 << k)) & (1u64 << k) > 0)) by (bit_vector);

        // Clear bit function properties
        // If the bit was previously cleared, clearing the bit does NOT change anything.
        assert(forall|i: u64, k: u64| #![auto] k < 64 ==> (i & (1u64 << k) == 0 <==> i & !(1u64 << k) == i)) by (bit_vector);
        // If the bit was not previously cleared, clearing the bit subtracts 2^k.
        assert(forall|i: u64, k: u64| #![auto] k < 64 ==> (i & (1u64 << k) > 0 <==> i & !(1u64 << k) == sub(i, 1u64 << k))) by (bit_vector);
        // Clearing the bit, whether changing anything or not, always results in the bit reading 0 afterwards.
        assert(forall|i: u64, k: u64| #![auto] k < 64 ==> ((i & !(1u64 << k)) & (1u64 << k) == 0)) by (bit_vector);

        // Relationship between bitshifting and addition
        assert(forall|i: u64, k: u64| #![auto] k < 63 ==> (i << k) << 1u64 == i << add(k, 1u64)) by (bit_vector);

        // Generate trailing zeroes function
        assert(forall|j: u64, k: u64| j < 64 && k < j ==> (u64::MAX << j) & (1u64 << k) == 0) by (bit_vector);
        assert(forall|j: u64, k: u64| j < 64 && k >= j && k < 64 ==> (u64::MAX << j) & (1u64 << k) > 0) by (bit_vector);

        // Generate trailing ones function
        assert(forall|j: u64, k: u64| j < 64 && k < j ==> !(u64::MAX << j) & (1u64 << k) > 0) by (bit_vector);
        assert(forall|j: u64, k: u64| j < 64 && k >= j && k < 64 ==> !(u64::MAX << j) & (1u64 << k) == 0) by (bit_vector);

        // is_allocated properties
        assert(forall|j: u64, k: u64| k < 64 ==> (j & (1u64 << k) == 0) || (j & (1u64 << k) > 0));
        assert(forall|j: u64, k: u64| k < 64 && (j & (1u64 << k) == 0) ==> j <= sub(u64::MAX, 1u64 << k)) by (bit_vector);
        assert(forall|j: u64, k: u64| k < 64 && (j & (1u64 << k) == 0) ==> j < u64::MAX) by (bit_vector);
        // assert(forall|j: u64| (#[trigger] j) < u64::MAX ==> exists|k: u64| k < 64 && (#[trigger] (j & (1u64 << k)) == 0)) by (bit_vector);
        // assert(forall|j: u64| #[trigger] (forall|k: u64| k < 64 && (#[trigger](j & (1u64 << k)) > 0)) ==> j == u64::MAX) by (bit_vector);
        // assert(forall|j: u64, k: u64| k < 64 && (j & (1u64 << k) == 0) ==> j < u64::MAX) by (bit_vector);


        // assert(forall|j: u64| j < 64 ==> !u64::MAX & (1u64 << j) == 0) by (bit_vector);


        // assert(forall|j: u64, k: u64| j < 64 && k < j ==> (u64::MAX << j) & (1u64 << k) == 0) by (bit_vector);


        // assert(forall|j: u64| j < 64 ==> !u64::MAX & (1u64 << j) == 0) by (bit_vector);
        
        
        // assert(forall|j: u64, k: u64| j < 64 && k < j ==> (1u64 << j) & (1u64 << k) == 0) by (bit_vector);
    }
    
}