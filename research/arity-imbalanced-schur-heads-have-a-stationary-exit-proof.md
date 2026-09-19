---
rg: 2
id: arity-imbalanced-schur-heads-have-a-stationary-exit-proof
kind: route
title: Combine unital full-block rigidity with the regular stationary type vector
target: arity-imbalanced-schur-heads-have-a-stationary-exit
requires:
  - binary-schur-head-embeddings-are-relative-inner-holonomies
  - finite-packet-graph-atlases-have-a-regular-stationary-flow
---

For a unital map `M_n(k)->M_n(k)^m`, coordinate projection gives `m`
unital endomorphisms of `M_n(k)`.  Each is inner, so every child is a faithful
copy.  This is the first alternative in the claim and rules out a literal
two-full-children/zero-third-child Morita wire.

If the third child is instead retained in the packet algebra and merely
renamed an exit, all ordinary subgroup identifications and stable-letter
packet automorphisms form a finite graph of finite groups.  Put the regular
stationary type vector of
`finite-packet-graph-atlases-have-a-regular-stationary-flow` on that graph.
It gives an exact finite-dimensional representation satisfying every wire.
Every nonzero packet type, including the exit, occurs positively.  Transitive
branch symmetry makes the three child traces equal, hence gives the displayed
`2/3` returned and `1/3` exit proportions at zero defect.

Therefore a normalized-HS bound charging the exit by relator energy fails on
this exact representation.  Direct sum amplification leaves its normalized
trace proportions and its zero defects unchanged.  A conjugacy that actually
identifies the whole parent projection with the two-child subprojection is an
additional rank-killing relation, and groupifying and stabilizing that
relation is exactly the missing payment rather than a consequence of the
ternary head.  This proves the claim for `m=3`; replacing three equal branches
by `m` gives the stated `r/m` and `(m-r)/m` version verbatim.
