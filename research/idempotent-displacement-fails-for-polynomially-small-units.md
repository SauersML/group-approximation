---
rg: 2
id: idempotent-displacement-fails-for-polynomially-small-units
kind: claim
title: A unit with 1 in the span of σ^{±1}, σ^{±2} displaces no idempotent in the (C4) sense, and one with σ + σ^{-1} = 1 displaces no idempotent at all; constant transvections, order-4 unipotents and Singer cycles in EL_3(F_2) ≤ G_X are of the first kind
artifacts:
  - research/artifacts/sk-cstar-idempotent-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).**

**Lemma.** Let `M` be a unital ring, `σ ∈ M^×` and `E` an idempotent with `Eσ^kE = 0` for all `k` in a finite `K ⊆ Z ∖ {0}`. If `1 = Σ_{k∈K} c_kσ^k` with central `c_k`, then `E = 0`.

**Consequences.**
- `E ⊥ σEσ^{-1}` ⟺ `EσE = Eσ^{-1}E = 0`. So if `σ + σ^{-1} = 1`, i.e. `σ^2+σ+1 = 0` in characteristic 2, no nonzero idempotent is displaced by `σ`.
- Condition (C4) of `unit-group-confined-subgroups-idempotent-commutator-lemma`, at `α = σ`, gives `Eσ^{±1}E = Eσ^{±2}E = 0`. So if `1 ∈ span_{F_2}{σ^{±1}, σ^{±2}}`, no idempotent displacement configuration exists for any confining set containing `σ`, in any ring containing `σ`.
- **Instances in `G_X = EL_3(LC(X,F_2)⋊_T Z)`**, all constant matrices in `EL_3(F_2)`:
  - every involution, including every transvection `e_ij(r)` (`σ^2 = 1`);
  - `I + E_12 + E_23` (`σ + σ^{-1} + σ^2 = I`);
  - Singer cycles of order 7 (`α, α^2, α^{-2}, α^{-1}` span `F_8 ∋ 1`).
- **Scope:** Le Boudec–Matte Bon's configurations for homeomorphisms exist whenever `σ^2 ≠ 1`. For unit groups the excluded class `B_4 = {σ : 1 ∈ span_{F_2}(σ^{±1}, σ^{±2})}` is strictly larger than the involutions.

**Proof:** `idempotent-displacement-obstruction-proof`.
