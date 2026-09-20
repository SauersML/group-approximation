---
rg: 2
id: wave5-detector-psl19-square-kernel-mod-three-proof
kind: route
title: Verify a characteristic-three projective generator and compute all25 distinct tensor types for the exact square kernel
target: wave5-detector-psl19-square-kernel-mod-three-acyclicity
requires:
  - wave2-detector-psl19-has-second-simple-quotient
  - wave4-detector-psl19-square-kernel-mod-five-acyclicity
artifacts:
  - research/artifacts/hyperbolic-rf-wave5-detectors-2026-09-20.md
  - experiments/hrf-wave5-detectors-2026-09-20/c5/module_input.json
  - experiments/hrf-wave5-detectors-2026-09-20/c5/projective_summands.json
  - experiments/hrf-wave5-detectors-2026-09-20/c5/isomorphisms.json
  - experiments/hrf-wave5-detectors-2026-09-20/c5/tensor_homology.py
  - experiments/hrf-wave5-detectors-2026-09-20/c5/generator.py
---

Use the same `Λ,Q,M` and exact four matrices `x12,x13,x23,y` as
in the required results. Put `k=F_3`, `C=<x12>` of order five, and
`P=k[Q/C]` of dimension684. Since five is invertible in `k`, `P`
is projective. Its averaging ideal is the whole group algebra:
starting from coset indicators and closing under right multiplication
by `x12,x13` gives exact ranks
`684,1367,2677,3402,3420`. Therefore the regular `k[Q]` is a direct
summand of copies of `P`, and the regular `k[Q²]` is a direct summand
of copies of `P⊗P`.

To construct tractable summands, exact enumeration identifies
`D=N_Q(C)` of order20 and `D/C=C_2²`. The four characters of this
quotient split `P` into four171-dimensional signed permutation
modules. Each is decomposed further by GAP, giving13 proposed
summands with dimensions

`18,36,36,81; 36,99,36; 36,36,99; 36,36,99`.

The certificate contains their bases inside the original684-dimensional
permutation module and all four generator matrices. The independent
Python verifier checks full basis rank684 and all52 intertwining
identities. GAP also proposes13 explicit isomorphisms to five
representative summands, with dimensions `18,36,81,36,99`. The
verifier checks matching square dimensions, invertibility and all
four intertwining equations for every isomorphism. Thus only25
tensor types must be calculated. No claim of indecomposability or
completeness from GAP is needed beyond these exact certificates.

For each tensor `V` the vertex and edge restrictions are projective,
so the invariant cellular cochain complex computes `H¹(Λ;V)`.
Writing `Ea` for the three edge fixed subspaces, the same exact
rank identity as in wave four, without the characteristic-five
simplification of edge dimensions, gives

`dim H¹(Λ;V)=sum_(a<b) rank(Ea+Eb)-rank(E1+E2+E3)
             -sum_a dim Ea+dim V^(Q²)`.

The edge fixed spaces are constructed using semisimple `C_5` modules.
Over `F_3`, `Φ_5` is irreducible of degree four, because the order
of three modulo five is four. Averaging over `C_5` gives the fixed
part. The complementary part splits into four-dimensional cyclic
blocks. The verifier checks each proposed cyclic block has dimension
four, obeys `1+g+...+g^4=0`, and that all blocks together form a basis.
For two nontrivial cyclic blocks with strings `v_k,w_k`, the four
vectors `sum_(k=0)^4 v_k⊗w_(k+s)`, `s=0,...,3`, span the fixed part
of their tensor product. Its dimension is four, since the simple
module is self-dual with endomorphism field `F_81`. Trivial-by-trivial
blocks each contribute one fixed vector; mixed blocks contribute
none. Full rank of every constructed edge basis is also checked.
The three generator pairs are the same specified
`(x12,x12),(x13,x13),(x23,y)`.

All25 resulting cohomology dimensions vanish. Hence
`H¹(Λ;P⊗P)=0`; projective generation and finite-index Shapiro yield
`H¹(M;k)=0`. The Euler characteristic already computed in wave four
is4,688,820, so the second-homology dimension is4,688,819.

For `1→C_5→M_c→M→1`, coefficients in `F_3` give
`H¹(M_c;F_3)=H¹(M;F_3)=0`, since `Hom(C_5,F_3)=0`.
Wave four gives zero first cohomology also with `F_5` coefficients
for every nonzero twist. A nontrivial finite solvable group has a
nontrivial abelianization and therefore a prime cyclic quotient.
If all prime divisors are three or five, either quotient contradicts
these two vanishings. This proves the stated mixed-prime solvable
refinement obstruction, with no conclusion for other prime divisors.

By the classical Burnside theorem, every finite group of order
`3^a 5^b` is solvable. Thus the stated exclusion also applies without
an explicit solvability assumption to every finite image, or finite
refinement kernel, whose prime divisors all lie in `{3,5}`. This
corollary imports precisely Burnside's two-prime solvability theorem.

**Independent review:** full argument and source reviewed PASS. The
auditor independently replayed the full generator computation and
the largest tensor `(4,4)`, including all three edge-basis rank checks
and all four span ranks. A separate replay also returned triple rank
5868. All25 recorded tensor results were assembled and their formula
identities checked. The root reviewer independently replayed the
actual group/coset input, direct-sum/isomorphism/cyclic-block
certificates and the optimized generator calculation. The other24
rank calculations were source/output reviewed, not all independently
repeated. See the wave-five audit receipt for that exact scope.
