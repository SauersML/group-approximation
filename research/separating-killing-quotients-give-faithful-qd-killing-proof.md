---
rg: 2
id: separating-killing-quotients-give-faithful-qd-killing-proof
kind: route
title: Sum matricial models of the killing quotient maps stage by stage, diagonalise, and apply Moutzouris Proposition 3.2
target: separating-killing-quotients-give-faithful-qd-killing
requires: [moutzouris-k0-killing-is-local, stw07-separating-qd-quotients-force-quasidiagonality]
artifacts:
  - research/artifacts/bk-rr0-trace-pushout-killing-part2-2026-09-13.md
---

Lemma R1, §1 of the artifact.

1. For fixed `k`, `Ψ_n = ⊕_{j≤n} ψ^{(j)}_{m(j,n)} ∘ ρ_{k,j}` is asymptotically
   multiplicative.  It recovers `sup_j ‖ρ_{k,j}(a)‖ = ‖a‖`, and has equal ranks
   on `e, f` whenever `[e]-[f] ∈ G_k`, because each summand realises the
   equivalence by partial isometries once `m(j,n)` is large.
2. Diagonalise over `k` to get a faithful `ρ : A -> Π M / ⊕ M` killing `G`.
3. `A` is quasidiagonal by
   `stw07-separating-qd-quotients-force-quasidiagonality`.  Moutzouris
   Proposition 3.2 (`moutzouris-k0-killing-is-local`) gives the embedding.
