---
rg: 2
id: separating-killing-quotients-give-faithful-qd-killing
kind: claim
title: A singular K_0-subgroup killed by a separating family of quasidiagonal quotient maps is killed by one faithful quasidiagonal embedding
distinct_from:
  stw07-separating-qd-quotients-force-quasidiagonality: that gets quasidiagonality from a separating family of quasidiagonal quotients; this also transports the killing of a K_0-subgroup to one faithful embedding.
  moutzouris-k0-killing-is-local: that imports the passage from asymptotic killing into Π M_k / ⊕ M_k to a quasidiagonal embedding; this produces the asymptotic killing from non-faithful killing maps.
artifacts:
  - research/artifacts/bk-rr0-trace-pushout-killing-part2-2026-09-13.md
---

**ESTABLISHED (Lemma R1 of the artifact; lane proof, not externally reviewed).**
Let `A` be separable and nuclear, and `G ⊆ K_0(A)` singular, exhausted by
finitely generated `G_k`.  Suppose that for each `k` there are \*-homomorphisms
`ρ_{k,j} : A -> D_{k,j}` into quasidiagonal algebras killing `G_k`, with
`∩_j ker ρ_{k,j} = 0`.  Then some faithful \*-homomorphism of `A` into a
quasidiagonal algebra kills `G`.

Mechanism: sum finitely many matricial models of the `ρ_{k,j}` at each stage,
diagonalise over `k`, then apply Moutzouris Proposition 3.2.  Ranks are compared
stage by stage, so no cancellation in any product target is needed.
