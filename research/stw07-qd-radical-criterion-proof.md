---
rg: 2
id: stw07-qd-radical-criterion-proof
kind: route
title: Apply compact-free extension permanence to the radical and Gabe's traceless corollary to its compact piece
target: stw07-qd-radical-criterion-compact-open
requires:
  - stw07-separating-qd-quotients-force-quasidiagonality
  - bk-no-compact-open-ideals-are-qd-invisible
  - gabe-traceless-exact-qd-af-embedding
artifacts:
  - research/artifacts/bk-spectral-extension-permanence-2026-09-12.md
---

**Criterion.**  If `E` is quasidiagonal, `R_qd(E) = 0`, whose spectrum is empty.
Conversely, `E/R_qd(E)` is quasidiagonal
(`stw07-separating-qd-quotients-force-quasidiagonality`) and nuclear.
`R_qd(E)` is exact as an ideal of a nuclear algebra.  If its spectrum is
compact-free, `bk-no-compact-open-ideals-are-qd-invisible` applied to
`0 -> R_qd(E) -> E -> E/R_qd(E) -> 0` makes `E` quasidiagonal.

**1.**  If `E` is not quasidiagonal, `Prim(R_qd(E))` has a nonempty compact open
subset `W`.  Let `K` be the ideal of `R_qd(E)` with `Prim(K) = W`.  It is an
ideal of `E`.  It is compact in the ideal lattice of `R_qd(E)`, and hence in that
of `E`: if `K ⊆ sup_i J_i`, then `K ⊆ sup_i (J_i ∩ R_qd(E))`, because ideal
intersection distributes over closed sums, so `K ⊆ J_i` for some `i`.

**2.**  `K` is separable and nuclear, and it is stably finite as an ideal of the
stably finite `E`.  If every lower semicontinuous trace on `K` were
`{0, ∞}`-valued, `K` would be traceless.  Gabe's Corollary C
(`gabe-traceless-exact-qd-af-embedding`, stably finite implies item 4) would
then say `Prim(K) = W` has no nonempty compact open subset.  But `W` itself is
one.

**3.**  For `E = (A ⊗ K)~`, the quotient `E/(A⊗K) = C` is quasidiagonal, so
`R_qd(E) ⊆ A ⊗ K`.
