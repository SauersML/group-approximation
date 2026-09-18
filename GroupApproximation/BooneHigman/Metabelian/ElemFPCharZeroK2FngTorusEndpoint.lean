import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngTorusOne
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngFourEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# `CZK2FngRankFourStatement` split at `m = 1` (lane `bh-met-92w`, endpoint)

Target: `CZK2FngRankFourStatement`, i.e. `K₂(4, ℤ[1/m])` is finitely normally generated in
`St_4(ℤ[1/m])` for all `m > 0`.  **Not closed.**

**Proved.**
* The matrix lemma `czK2FngTorus_projection_H_val`:
  `projection (H_ab(v)) = diag(v at a, v⁻¹ at b, 1 elsewhere)`.
* Pairwise commutation of the torus images, `czK2FngTorus_torusSet_commute`.
* The torus-stability step `czK2FngTorus_succ_of_le_sup`.
* `E_3(ℤ)` finitely presented and `K₂(3, ℤ)` finitely normally generated
  (`czK2FngTorus_k2ThreeOne_fng`).
* `czK2FngTorus_rankFour_of_stabOne_of_gtOne`, the reduction below.

**Remaining gap (LOUD).**
* `m = 1`: the residual `czK2FngTorus_StabOneStatement`.  It is true, it is not equivalent to
  anything already stated, and it is smaller in proof content than the `m = 1` slice (it needs
  no presentation of `SL_4(ℤ)`).  See `ElemFPCharZeroK2FngTorusOne`.
* `m > 1`: `czK2FngTorus_GtOneStatement`.  This is the fixed-torus form of
  `czK2FngFour_TorusStatement` restricted to `m > 1`.  **It is EQUIVALENT to the target
  restricted to `m > 1`** (`czK2FngTorus_gtOne_of_rankFour` proves one direction; the other is
  `czK2FngTorus_fng_of_le`).  It is not claimed as progress.
  Behr's theorem (`SL_4(ℤ[1/m])` finitely presented) remains the truth check only.
  Neither the symbols route nor any circular Higman interface enters.

So the lane's strictly smaller Statement is `czK2FngTorus_StabOneStatement` (the `m = 1` slice,
itself strictly weaker than the target), and the `m > 1` part is left exactly as open as before.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- The `m > 1` part in fixed-torus form.  **Equivalent** to the target restricted to `m > 1`. -/
def czK2FngTorus_GtOneStatement : Prop :=
  ∀ m : ℕ, 1 < m → ∃ S : Set (SteinbergGroup (Fin 4) (Localization.Away (m : ℤ))),
    S.Finite ∧ S ⊆ K2 (Fin 4) (Localization.Away (m : ℤ)) ∧
      K2 (Fin 4) (Localization.Away (m : ℤ)) ≤
        Subgroup.normalClosure S ⊔ Subgroup.closure (czK2FngTorus_torusSet 4 m)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngTorus_GtOneStatement

/-- **The reduction.**  The `m = 1` residual and the `m > 1` part give the target. -/
theorem czK2FngTorus_rankFour_of_stabOne_of_gtOne (h1 : czK2FngTorus_StabOneStatement)
    (hgt : czK2FngTorus_GtOneStatement) : CZK2FngRankFourStatement := by
  intro m hm
  by_cases h : 1 < m
  · obtain ⟨S, hS, hSK, hle⟩ := hgt m h
    exact czK2FngTorus_fng_of_le m S hS hSK hle
  · have hm1 : m = 1 := by omega
    subst hm1
    exact czK2FngTorus_one_of_stabOne h1

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngTorus_rankFour_of_stabOne_of_gtOne

/-- **Strength (LOUD).**  The `m > 1` part is implied by the target, so it is equivalent to the
target restricted to `m > 1`. -/
theorem czK2FngTorus_gtOne_of_rankFour (h : CZK2FngRankFourStatement) :
    czK2FngTorus_GtOneStatement := by
  intro m hm
  obtain ⟨S, hS, hSeq⟩ := h m (by omega)
  refine ⟨S, hS, ?_, ?_⟩
  · intro k hk
    rw [← hSeq]
    exact Subgroup.subset_normalClosure hk
  · rw [← hSeq]
    exact le_sup_left

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngTorus_gtOne_of_rankFour

/-- The residuals also give the `bh-met-92p` torus residual (via the target). -/
theorem czK2FngTorus_torus_of_stabOne_of_gtOne (h1 : czK2FngTorus_StabOneStatement)
    (hgt : czK2FngTorus_GtOneStatement) : czK2FngFour_TorusStatement :=
  czK2FngFour_torus_of_rankFour (czK2FngTorus_rankFour_of_stabOne_of_gtOne h1 hgt)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngTorus_torus_of_stabOne_of_gtOne

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
