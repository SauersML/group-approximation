---
rg: 2
id: thompson-v-r5-coherent-alternating-packet
kind: claim
title: Synchronize the Bleak--Quick R5 swap complex into a uniform alternating packet
artifacts:
  - research/artifacts/thompson-v-r5-coherent-alternating-packet-2026-08-21.md
distinct_from:
  thompson-v-one-word-strict-hs-ceiling: that is the scalar endpoint equivalent to nonhyperlinearity of V; this is a concrete uniform finite-packet compiler sufficient to prove it.
  affine-clone-model-defeats-pure-thompson-prefix-error-spreading: that exact countermodel covers context-local split, conjugacy, and leaf-permutation axioms; this claim requires global synchronization through the Bleak--Quick overlap and R5 collision cells.
  gowers-hatami-finite-group-hs-stability: that exactifies an all-pairs approximate map once supplied; this claim constructs such maps from one fixed V-presentation model with constants independent of packet size.
---

Fix the Bleak--Quick prefix-transposition presentation `V=<X|R>` with relation
families R1--R5, and let `a=(00 01)`.  Prove constants `C,delta_0>0`,
independent of matrix dimension and depth, with the following property.

For every tuple `U in U(d)^X` with `def_R(U)<=delta_0` and every `n>=3`, put
`N=2^n` and let `a_N in A_N` be the permutation induced by `a` on the
length-`n` cylinders.  There is a map `Phi:S_N->U(d)` such that

```text
Phi(1)=I,
max_(g,h in S_N)||Phi(gh)-Phi(g)Phi(h)||_2 <= C def_R(U),       (CAP1)
||Phi(a_N)-U(a)||_2 <= C def_R(U).                             (CAP2)
```

The proposed proof uses redundant swap names on the complete transposition
complex: overlap cells on triples, R4/R5 disjoint-collision cells on
four-subsets, and R3 for the marked coarse split.  The Johnson graph `J(N,2)`
has a uniform normalized spectral gap, suggesting a uniform linear gauge
synchronization estimate.  The open steps are to derive the whole normalized
cell energy from bounded-use conjugates of R1--R5 and to lift the linear
synchronization nonabelianly without a depth-dependent loss.

More locally, put one `S_4` chart on each four-subset.  Adjacent charts lie in
a five-set.  Audit whether every shared-edge comparison in such a five-set,
after one common conjugation, is a bounded-use depth-three consequence of R2,
R4, and R5.  For a fixed edge the context graph is `J(N-2,2)`, with uniform
normalized spectral gap, so a positive local audit would give averaged HS
gauge synchronization.  Upgrading that averaged estimate to compatible
unitary edge names, the marked R3 comparison, and the all-pairs bound `(CAP1)`
is still open.

As a fast falsification test, form the normalized linearized occurrence
boundary `D_n` and track its least nonzero singular value.  Decay to zero rules
out this compiler.  A uniform gap is necessary but not sufficient, because
the nonlinear HS lifting would remain.

This full-table CAP claim is now a stronger fallback.  The preferred weaker
target is `thompson-v-r5-coherent-carmichael-family`, which retains only an
unbounded family of conjugate order-three generators and their pairwise
Carmichael relators.  Compact packing closes that weaker target without
finite-group exactification.
