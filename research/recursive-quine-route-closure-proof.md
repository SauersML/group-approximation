---
rg: 2
id: recursive-quine-route-closure-proof
kind: route
title: Sofic permanence for the two families, and the constant compiler for the fixed point
target: recursive-quine-route-to-kaplansky-is-closed
requires:
  - leavitt-two-compressor-core-is-lef-and-marked-operator-mf
  - recursive-leavitt-kernel-packets-are-locally-finite
  - subgroup-supported-one-sided-inverse-rigidity
artifacts:
  - research/artifacts/kaplansky-cross-atlas-affine-lift-2026-09-07.md
---

## Proof

### The recursive families

A LEF group is sofic, and a locally finite group is LEF, so both the
elementary two-compressor core and every stage of the recursive kernel packet
tower are sofic.  Elek--Szabo prove that `k[H]` is directly finite for every
sofic `H` and every field `k`; in particular for `k = F_2`.  Now let
`alpha in F_2[Q]` have support inside such an `H`.  By
`subgroup-supported-one-sided-inverse-rigidity` with `f = 1`, if any
`beta in F_2[Q]` satisfies `beta alpha = 1`, then `alpha` is already
invertible in `F_2[H]`, so `alpha beta = 1` as well and the pair is not a
counterexample.  The exclusion is therefore unbounded in support, not a
finite fence.

Two corollaries recorded elsewhere are instances of this: symmetric
compressor sums are square-zero packets, and a one-packet correction is
impossible, both of which the packet-trace artifact derives directly.

### The compiler

Backward direction.  Suppose a counterexample `(P, Q)` exists.  The constant
map `e |-> (P, Q)` is total computable and satisfies the halting clause
vacuously, since the pair is a one-sided inverse pair whether or not `e`
halts.  So a compiler exists.

Forward direction.  Suppose a compiler exists.  Apply it to any index that
provably halts.  Its output is a finite pair of subsets of `Q` which is a
genuine one-sided inverse pair, and whether the reverse product is the
identity is decided by finitely many exact multiplications in the binary
prefix normal form.  Either it is not, and the counterexample is in hand, or
it is, contradicting that the compiler's output is one-sided.

So the two existence statements are equivalent, and the backward direction is
the vacuous one — exactly as in
`canonical-reverse-kleene-compiler-is-goal-equivalent`.  The equivalence is
the content: it says building the compiler is not a way of avoiding the
construction, because it *is* the construction.  A fixed point can force the
logical diagonal; it cannot invent the finite convolution identity that the
diagonal would need to print.
