---
rg: 2
id: thompson-v-r5-coherent-carmichael-family
kind: claim
title: Compile arbitrarily large Carmichael families from the Bleak--Quick R5 presentation
artifacts:
  - research/artifacts/thompson-v-r5-coherent-alternating-packet-2026-08-21.md
distinct_from:
  thompson-v-r5-coherent-alternating-packet: that asks for an all-pairs approximate multiplication table for an entire leaf symmetric group; this asks only for conjugate order-three generators and their pairwise Carmichael relators.
  affine-clone-model-defeats-pure-thompson-prefix-error-spreading: that realizes context-local clone and finite leaf-permutation packets with private gauges; this claim requires all Carmichael generators to be literal matrix conjugates of one fixed Bleak--Quick generator in a single presentation model.
  gowers-hatami-finite-group-hs-stability: no finite-group exactification is used here; compact packing in the original matrix dimension is enough once the Carmichael family exists.
---

In the Bleak--Quick presentation let `b=(01 10 11)`.  Prove constants
`C,delta_0>0`, independent of family size and matrix dimension, such that the
following holds.

For every tuple `U in U(d)^X` with `def_R(U)<=delta_0` and every integer
`M>=2`, there are unitaries `W_1,...,W_M in U(d)` for which

```text
X_i=W_i U(b) W_i^*,
||X_i^3-I||_2 <= C def_R(U),
||(X_i X_j)^2-I||_2 <= C def_R(U)       for i!=j.        (CCF)
```

These are precisely the defining relator shapes in Carmichael's presentation

```text
A_(M+2)=<x_1,...,x_M | x_i^3=(x_i x_j)^2=1, i!=j>,
```

where the standard model is `x_i=(i,M+1,M+2)` (equivalently
`(1,2,i+2)` after relabelling).

The proposed Thompson construction chooses many common-pivot three-cycles on
clopen pieces.  Each is a group conjugate of `b`; the open quantitative step
is to choose the conjugating words so every pair relation in `(CCF)` is a
bounded-use consequence of the fixed R1--R5 relations, uniformly in `M`.
Only the Carmichael star is needed.  No consistent names for arbitrary
permutations and no multiplication table for `A_(M+2)` are required.

The exact group geometry is available.  Choose a finite maximal prefix code
`P={p_1,...,p_(M+2)}`.  The prefix replacements permuting the cylinders in
`P` give a copy of `S_(M+2)` in `V`, and

```text
x_i=(p_i p_(M+1) p_(M+2))
```

obey the Carmichael relations.  Each `x_i` is conjugate in `V` to `b` after
refining the source and target prefix partitions: both are one three-cycle on
clopen Cantor pieces with a nonempty clopen fixed complement.  What is not
automatic is a choice of finite-presentation words whose conjugacy and all
pair relations have uniformly bounded R1--R5 defect cost.

A concrete word-level formulation uses the local `S_4` packet in R1.  If `a`
is its transposition generator, then `b` and `b^a` are common-pivot
three-cycles and `(b b^a)^2=1`.  Seek words `g_i` such that every relative word
`g_i^(-1)g_j` admits, with bounded R1--R5 cost, a factorization through the
double coset

```text
C_V(b) a C_V(b^a).
```

The two centralizer factors should be certified by literal conjugates of the
R4/R5 disjoint-support commutators.  Then
`X_i=U(g_i)^*U(b)U(g_i)` are globally fixed names while every pair relation
reduces to the one R1 relation `(b b^a)^2`.  Constructing arbitrarily large
such certified cliques with a uniform word-defect budget is the remaining
group-theoretic target.

The strongest literal version of this paragraph is impossible by
`literal-one-cell-carmichael-cliques-are-uniformly-finite`: the edge words for
an unbounded family cannot each be freely equal to one conjugate from a fixed
finite template list.  A viable double-coset proof must therefore use a
bounded configuration of several relator cells whose long conjugating
boundaries cancel, or prove an averaged synchronization inequality.  Merely
choosing a pair-specific transporter and declaring its edge relation a
renamed R1/R5 cell does not close the global-name problem.

The affine-clone model remains a mandatory firewall: finite leaf permutation
packets can realize the Carmichael relator shapes locally.  Thus a proof must
use their simultaneous realization as literal conjugates of the one fixed
word `U(b)` in a model of the whole Bleak--Quick presentation, rather than
independent context gauges.

There is now an exact smaller target.  The route
`thompson-v-common-frame-carmichael-reduction` shows that it is enough to
certify two stabilizer corrections for each pair: one disjoint transposition
and one disjoint three-cycle.  If those centralizer loops have R1--R5 area at
most `C`, the pair relator has area at most `4C+A_0`, where `A_0` is the fixed
local-S4 area.  Thus all finite-permutation algebra is constant-cost; the
remaining problem is solely the uniform address-coherence statement
`thompson-v-r5-uniform-common-pivot-centralizers`.
