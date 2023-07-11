# Bit field verification for Theseus

To keep track of allocated memory units in Theseus, we use bit fields represented as slices of `AtomicU64`s. Each bit represents 
a single unit of memory of some predetermined size. We seek to verify this bit field bookkeeping using formal verification tools 
such as [Prusti](https://github.com/viperproject/prusti-dev). Note that in this proof-of-concept repository we use the simple 
single-threaded `u64` type instead of `AtomicU64`.

## Why is verifying this challenging?

- The formal verification tool we use, Prusti, only has rudimentary and experimental support for bitwise operations.
- Working around this using lists is unproductive, as this requires memory allocation in the first place and thus creates a 
circular dependency.
- `second_impl` and `third_impl` provide two potential approaches to verification.

## First implementation

See in `first_impl`.

NOTE: This first implementation is pretty useless as it functions basically like a stack: the verification conditions assumes 
deallocations only from the latest allocated bit downward.

## Second implementation

The second implementation starts with some observations about the mathematical properties of bit operations on unsigned `u64` 
integers. Given a `u64`, `u`:

- `u` has 64 bits indexed from `0` through `63`.
- Flipping a bit at index `i` is equivalent to adding or subtracting `2^i` to/from `u`.
- Given some bit at index `i`, all previous bits (bits at indices less than i) add up
to `2^i - 1` when all flipped (we can understand this intuitively in base 10 as the number
immediately before 1000 being 999, for example). When we have `i = 0`, then `2^i - 1 = 2^0 - 1 = 0`.
- Given some bit at index `i`, flipping any subsequent bit (bits at indices greater
than i) is adding or subtracting an "even multiple" of `2^i` ("even multiple" here meaning
the number can be written as `2k * 2^i` where `k` is some non-negative integer - is there a better term for this?)
to/from `u`.

Given the above observations, we can approximate bitvector operations using mathematical expressions that Prusti understands.
The downsides of this approach are:

- To ensure airtight verification, we need to prove the above conjectures as formal properties of bitvector operations. There is
no way to do this in Prusti, hence we need to fall back on pen and paper.
- Lack of existing Prusti lemmas for the power or logarithm functions means that we need to write trusted Prusti postconditions for these ourselves.

## Third implementation

The third implementation makes use of another verification tool, Verus, in addition to Prusti. We use Verus to verify some 
bit vector properties 

## Properties and invariants

## Second implementation properties

The second implementation accomodates cases where we do not necessarily have contiguous `1`s and `0`s in the bit field. This is more realistic as the operating system will be constantly deallocating memory as well, and not necessarily in the order of allocation. Again, we split the original `first_fit()` function into a `first_fit_in_u64()` function that upholds the following properties:

- It only accepts bit fields that are non-full, i.e., with a value less than `u64::MAX`.
- Since the bit field is non-full, we _must_ be able to allocate a new memory block inside (memory alignment and overlap with metadata notwithstanding). As long as the previous condition is guaranteed, `first_fit_in_u64()` should not need the `Option<T>` wrapper.

To find such index, we use the bitwise `u64::trailing_ones()` function. We make a wrapper around this function that verifies the following properties:

- The input bit field is less than `u64::MAX`.
- The output `idx` should be the first index where the bit is 0. This is verified by calculating 
- `first_fit` should return the first free address / bit index. This is verified with the following invariants:
    - fewfe

