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

The third implementation makes use of another verification tool, Verus, in addition to Prusti. We use Verus to verify some bit
bitfield properties using its `bit_vector` verifier. We verify properties for the following functions: `power_of_2`, `set_bit`, 
`clear_bit`, `make_trailing_zeroes`, `make_trailing_ones`, and `is_allocated`. These verified properties are then put into Prusti 
as trusted postconditions (assertions that Prusti will accept without verifying). We then proceed to prove the remaining functions
for bitfield operations the same way as we did for the second implementation. The advantages of this approach are:

- More optimized than the second implementation, since we are not reliant on expensive arithmetic logarithm and power functions.
- More airtight, no manual pen-and-paper proof needed.

## Next steps

- Create a model for `AtomicU64` that can be verified by Prusti and that can be subtituted for the actual `AtomicU64` used in    
Theseus. I currently have some difficulty doing this because Prusti doesn't seem to play very nicely with references to generic
types.
- Integrate this with the existing bitfield infrastructure in Theseus.

## Prusti configuration

Last verified successfully 14 July 2023 on Ubuntu 22.04.2 LTS, x86_64. Prusti VSCode extension using `LatestRelease` build option. Environment
options:

```
"prusti-assistant.extraPrustiEnv": {
    "PRUSTI_CHECK_OVERFLOWS": "false",
    "PRUSTI_ENCODE_BITVECTORS": "true",
    "PRUSTI_ASSERT_TIMEOUT": "40",
    "PRUSTI_MIN_PRUSTI_VERSION": "0.2.1",
    "PRUSTI_ENABLE_TYPE_INVARIANTS": "true"
},
```

Verified successfully on a M1 Mac with the same environment options after uncommenting line 277 of `third_impl/mod.rs` (verification _might_ also pass on Linux x86 with this line uncommented). Prusti set up on M1 following the workaround described [here](https://github.com/viperproject/prusti-dev/issues/1193#issuecomment-1312956882). The version of Prusti used is the stable release from 26 January 2023.