---
rg: 2
id: thompson-v-r5-uniform-common-pivot-centralizers
kind: claim
title: Certify an unbounded common-pivot packet by uniformly bounded R5 centralizer cells
refuted_by: finite-mark-centralizer-commutator-area-is-proper
artifacts:
  - research/artifacts/thompson-v-r5-coherent-alternating-packet-2026-08-21.md
distinct_from:
  thompson-v-r5-coherent-carmichael-family: that asks directly for all pairwise Carmichael relators among globally named conjugates; this isolates the strictly smaller address-coherence statement to which a common-frame calculation reduces that compiler.
  affine-clone-model-defeats-pure-thompson-prefix-error-spreading: that realizes contextwise prefix packets with independent gauges; this requires two families of centralizer loops for one fixed shallow three-cycle to have uniformly bounded area in the single Bleak--Quick presentation.
  thompson-v-r5-coherent-alternating-packet: that asks for coherent names and multiplication on an entire leaf symmetric group; this asks only for the two stabilizer corrections occurring in a common-pivot pair alignment.
  cyclic-centralizer-slow-twist-has-linear-filling-area: that proves linear area growth when one commutation seed is transported inside an isolated cyclic centralizer; this asks whether the full R2/R3 transport and split relations provide a genuinely ambient shortcut unavailable in that presentation.
  finite-mark-centralizer-commutator-area-is-proper: that uses a nontrivial local coefficient over the marked-subgroup Schreier graph to prove that even arbitrary ambient R1--R5 diagrams have unbounded area on the required infinite family; it decisively refutes this claim.
---

This target is false.
`finite-mark-centralizer-commutator-area-is-proper` gives an ambient
R1--R5 filling-area lower bound which diverges on the displayed swaps.

Fix four shallow leaves `p,q,c_0,c_1` in one finite prefix chart and put

```text
b_0=(p q c_0).
```

Find a constant `C` such that, for every `M`, there are further pairwise
disjoint prefix leaves `c_2,...,c_M` and word representatives of

```text
s_(ij)=(c_1 c_j),
t_(ij)=(c_1 c_i c_j)                    (2<=i!=j<=M)
```

for which

```text
Area_(R1--R5)([b_0,s_(ij)])<=C,
Area_(R1--R5)([b_0,t_(ij)])<=C.          (UCP)
```

Both correction permutations are geometrically disjoint from the support of
`b_0`, so the loops are trivial in `V`.  The content is the area bound,
uniform in the number and depths of the chosen leaves.  Abstract conjugacy of
disjoint-support configurations does not prove `(UCP)`: changing a contextual
name to a single global word introduces precisely these stabilizer loops.

R5 is the final Bleak--Quick seed for disjoint prefix transpositions.  A
positive proof may therefore establish a still more primitive bound for the
particular disjoint-swap commutators appearing after writing `b_0` and
`t_(ij)` as products of two prefix transpositions.  A derivation whose number
of R2/R3 transport cells grows with address depth is insufficient.

There is a quantitative firewall against the most direct iteration.
`cyclic-centralizer-slow-twist-has-linear-filling-area` constructs exact
order-three block matrices for which one shallow commutator has defect
`O(1/j)` but its depth-`j` conjugation loop has defect `3/2`.  Thus no bounded
number of copies of the shallow centralizer cell can certify `(UCP)`.  Any
positive proof must use R2/R3 to leave the cyclic centralizer, cancel the
address holonomy in the ambient presentation, and return at constant cost.

The most obvious *trivial-coefficient* negative certificate is unavailable.  By
`thompson-v-central-extensions-split`, `V` is integrally acyclic in degrees
one and two, so a conjugation-invariant abelian phase or signed count of R5
cells cannot define a nontrivial central extension class detecting depth.
By itself this does not decide `(UCP)`: a negative result must instead use a nontrivial
relation-module coefficient system or a genuinely nonabelian corridor
invariant.  It rules out treating the visible number of R5 cells in one
chosen derivation as an invariant lower bound.

The required negative certificate instead exists with nontrivial
coefficients.  `finite-mark-centralizer-commutator-area-is-proper` induces a
nontrivial character of `<b_0>` to the Schreier graph `<b_0>\V`.  It proves
that the area of `[b_0,h]` grows with the distance of the centralizer coset
`<b_0>h`.  The distinct swaps `s_(ij)` escape every bounded Schreier ball, so
their areas cannot obey `(UCP)`, even when fillings use all R1--R5 cells.
