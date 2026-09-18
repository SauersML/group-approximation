---
rg: 2
id: amenable-cd-two-rank-gap-via-l2-finite-weak-bass
kind: route
title: The weak Bass inequality for countably generated projectives of finite L2-dimension, applied to the relation module, gives b_1 = 1 + b_2 and hence the L2-rank gap for amenable groups of cd 2
target: amenable-cd-two-groups-have-an-l2-rank-gap
requires:
  - amenable-cd-two-bass-defect-equals-euler-characteristic
  - l2-finite-projectives-over-amenable-groups-satisfy-weak-bass
  - amenable-cd-two-kropholler-iff-locally-indicable
---

**Status: a reduction (one direction).** The target follows from the open statement
`l2-finite-projectives-over-amenable-groups-satisfy-weak-bass` (WBB). The converse is not known,
because WBB is about all countably generated projectives and the target controls only relation
modules.

**Argument.** Let `G` be an infinite, finitely generated amenable group with `cd_Z G <= 2`, and
choose `n` generators. `G` is torsion-free because its cohomological dimension is finite. The
relation module `P = ker(Z[G]^n → Z[G])` is a countably generated projective module, and
`dim_U(U ⊗ P) = n − 1 < ∞`. Both facts are item 1 of
`amenable-cd-two-bass-defect-equals-euler-characteristic`. So WBB applies to `C = P`, and gives
`rank_Q(Q ⊗ P) <= dim_U(U ⊗ P)`. This is statement (d) of item 2 there, for every such `G`.
Item 2 gives (d) ⇒ (a), Kropholler's question in dimension at most 2. Item 2(a) of
`amenable-cd-two-kropholler-iff-locally-indicable` gives (a) ⇒ the target, with `c = 1`.

**Which case is needed.** Only the counterexample case is needed: `G = K` with finite
abelianization, and `C` the core `P'` with no finitely generated summand, where
`D(P') = 1 + b_2(K)`. This is item 3 of the claim.

**Why this route is not already dead.** The claim proves that three routes to WBB are dead:
finite truncations (item 4), colimits of free modules and flat approximations (item 5), and
`L²`/Følner data (item 6). WBB itself is not refuted by any of these. They say only that a proof
has to use the projectivity of `C` globally.
