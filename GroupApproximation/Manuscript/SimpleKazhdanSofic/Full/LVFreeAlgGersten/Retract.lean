import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFreeAlgK2.Augmented
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStableK2.Reduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Retracts of augmentation nil parts of stable `K₂` (lane sk-ger-01)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii, route W1.

The nil part `AugNilK2Trivial π` of stable `K₂` (lane LVNK1, `LVFreeAlgK2.Augmented`) passes
to retracts of augmentations.  Take a square of rings

```
  S --i--> R --r--> S          (r ∘ i = id)
  |ρ       |π
  B --j--> A                   (π ∘ i = j ∘ ρ)
```

If `k ∈ K₂(n, S)` satisfies `ρ_* k = 1`, then `i_* k ∈ K₂(n, R)` satisfies
`π_* (i_* k) = j_* (ρ_* k) = 1`, so `i_* k` dies after padding; applying `r_*` (which commutes
with padding) kills `k = r_* (i_* k)` after the same padding.

This is the formal core of the Swan–Weibel deformation trick used in
`LVFreeAlgGersten.Residual`: for `R = S[t]`, `π = (t ↦ 0)`, a deformation `i = ψ` with
`(t ↦ 1) ∘ ψ = id` and `(t ↦ 0) ∘ ψ = const ∘ aug` makes the augmentation nil part of `S` a
retract of `NK₂(S)`.
-/

namespace GroupApproximation.Full.LVFreeAlgGersten

open SteinbergGroup

/-- **Retract transfer of the augmentation nil part.**  If `ρ : S → B` is a retract of
`π : R → A` along a ring map `i : S → R` with left inverse `r`, and `π ∘ i` factors through `ρ`,
then vanishing of the nil part of `π` gives vanishing of the nil part of `ρ`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii, route W1.) -/
theorem skGer_augNil_of_retract {R A S B : Type*} [Ring R] [Ring A] [Ring S] [Ring B]
    (π : R →+* A) (ρ : S →+* B) (i : S →+* R) (r : R →+* S) (j : B →+* A)
    (hri : r.comp i = RingHom.id S) (hsq : π.comp i = j.comp ρ)
    (hN : LVFreeAlgK2.AugNilK2Trivial π) : LVFreeAlgK2.AugNilK2Trivial ρ := by
  intro n k hk hρ
  have hi : projection (ringMap i k) = 1 := by
    rw [LVCohnK2.projection_ringMap, hk, map_one]
  have hπ : ringMap π (ringMap i k) = 1 := by
    rw [LVCohnK2.ringMap_ringMap i π k, hsq, ← LVCohnK2.ringMap_ringMap ρ j k, hρ, map_one]
  obtain ⟨N, hnN, hNk⟩ := hN n (ringMap i k) hi hπ
  refine ⟨N, hnN, ?_⟩
  have hk1 : ringMap r (ringMap i k) = k := by
    rw [LVCohnK2.ringMap_ringMap i r k, hri, LVCohnK2.ringMap_id_apply]
  rw [← hk1, LVStableK2.indexMap_ringMap, hNk, map_one]

#audit_axioms GroupApproximation.Full.LVFreeAlgGersten.skGer_augNil_of_retract

end GroupApproximation.Full.LVFreeAlgGersten
