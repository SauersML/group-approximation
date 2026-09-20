# Wave five: characteristic-three control of the specified square kernel

Date:2026-09-20. Hyperbolic residual finiteness remains open.

The target of this bounded computation is the full first mod-three
homology of the exact kernel `M=ker(Λ→PSL_2(19)²)` from wave two.
It uses the projective-generator method from wave four with a
new subgroup and new coefficient field. This is not merely a test
of one additional selected cover.

**Status:** complete25-pair computation and independent review PASS.
The established theorem is
[[wave5-detector-psl19-square-kernel-mod-three-acyclicity]], with full
argument in [[wave5-detector-psl19-square-kernel-mod-three-proof]].
The complete records are assembled by `c5/collect_results.py`.
The auditor replayed the full generator and largest tensor, including
all edge-basis ranks, and checked all25 output identities. The root
reviewer independently replayed the group/coset input, module and
isomorphism certificates, cyclic blocks and optimized generator.
The other24 tensor ranks received source/output review; independent
full recomputation of those24 is not claimed.

## The failed smaller generator and the successful replacement

In characteristic three, neither the order12 subgroup A4 nor the
order171 Borel supplies the projectivity used in wave four. The
normalizer `D=N_Q(C_5)` has order20 prime to three. Its coset module
has dimension171 and decomposes into dimensions18,36,36,81. All16
tensor cohomology sectors vanish, but the averaging ideal has
ranks171,341,681,1361,2091,2411,2411. Thus it misses part of the
group algebra and cannot prove full-kernel vanishing.

Replace `D` by `C=C_5`. The684-dimensional permutation module
`P=F_3[Q/C]` is projective and is a generator: its averaging ideal
has ranks684,1367,2677,3402,3420. This covers every group-algebra
component, including those omitted by the first probe.

To avoid an expensive direct684-dimensional decomposition, use
`D/C=C_2²`. Its four characters split P into four171-dimensional
signed permutation modules. Their13 proposed GAP summands have
five isomorphism types, of dimensions18,36,81,36,99. Stored basis
and isomorphism matrices are verified independently over F3:
full basis rank684, all52 generator intertwining identities,
and13 square invertible isomorphisms with all four intertwining
identities each. The actual PSL19 group and coset action are also
reconstructed and compared field by field with stored input.

For each of25 tensor types, exact semisimple C5 block decompositions
construct the three edge fixed spaces. Four span-rank computations
and the global fixed dimension determine H1. The largest tensor
has9801 coordinates. Each --only invocation independently checks
all input and module certificates before computing its selected pair.

The original all-pairs process completed22 pairs before exiting143
at roughly120seconds without a mathematical error. The final three
pairs completed individually with zero cohomology. The largest has
edge dimensions1961 each, pair ranks3917 each, triple rank5868 and
global invariant dimension zero. Its complete independent replay
finished in140seconds; separate rank stages also corroborate it. A direct GAP684 decomposition also
exited143 without output; the exact four-character split replaces
that computational step. These process terminations are not used
as evidence for or against any mathematical claim.

## Established consequence and remaining gap

The complete verified computation gives `H_1(M;F_3)=0`. Combining
it with established mod-five vanishing excludes every nontrivial
finite solvable image of M with prime divisors only three and five.
The same holds for nonzero twisted preimages: central C5 adds no
first F3-cohomology, and wave four already controls F5-cohomology.
By Burnside's classical two-prime solvability theorem, every finite
group whose prime divisors lie in `{3,5}` is solvable. Thus the result
excludes all refinement kernels supported on those two primes.

It does not imply integral perfectness. Quotients introducing two,
nineteen or other primes, and arbitrary nonsolvable refinements,
remain uncontrolled. No finite central detector is constructed.

## Reproducibility

All files are under `experiments/hrf-wave5-detectors-2026-09-20/`.
The root directory records the insufficient D20 probe. The `c5/`
subdirectory holds the full-generator computation.

Use Python3.13.13, python-flint0.9.0 and NumPy2.5.3:

```
/tmp/hrf-wave2-py313/bin/python experiments/hrf-wave5-detectors-2026-09-20/c5/verify_input.py
/tmp/hrf-wave2-py313/bin/python experiments/hrf-wave5-detectors-2026-09-20/c5/generator.py
/tmp/hrf-wave2-py313/bin/python experiments/hrf-wave5-detectors-2026-09-20/c5/tensor_homology.py --only 4 4
```

Run the final command for each pair i,j in0,...,4, or omit --only
in an environment allowing the whole run. GAP is unnecessary for
verification. Its optional proposal-generation scripts are
`split_normalizer.py`, `split_decompose.g`, `deduplicate.py` and
`isomorphisms.g`. The group input is regenerated by `construct.py`.

All arithmetic is exact. Before matrix products the int64 entries
lie in0,1,2, with dimension at most99 in the factor computations;
intertwining also has only684 coordinates. Tensor orbit sums have
five bounded outer-product terms. These bounds are far below
integer overflow. All span ranks use nmod_mat over F3.

The optimized generator computation stops at rank3402 and computes
the new right-translation span in the18-dimensional quotient. It
has rank18, completing the3420-dimensional ideal. This avoids a
redundant final large row reduction; both independent reviewers
replayed the optimized full calculation successfully.
