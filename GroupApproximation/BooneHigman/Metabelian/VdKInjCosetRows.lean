import GroupApproximation.BooneHigman.Metabelian.VdKInjCosetSurj
import GroupApproximation.BooneHigman.Metabelian.VdKInjDirectTrans
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowCoset
import GroupApproximation.Meta.AxiomGuard

/-!
# Parabolic cosets and unimodular rows

Lane `bh-met-91j`, third file.  `VdKRowCoset n R` is the set of right cosets `P g` of the
parabolic image `P = vdkRowParSubgroup n R` in `St_{n+1}(R)`.

* `vdkInjCoset_rowOf g = e_last ᵥ* M_g`, the last row of the matrix of `g`.
  `vdkInjCoset_rowOf_eq_iff`: `rowOf a = rowOf b ↔ b a⁻¹ ∈ rowStab`.
* `vdkInjCoset_rowMap : VdKRowCoset n R → R^{n+1}`, `P g ↦ e_last ᵥ* M_g`.  It is well defined
  because `P ≤ rowStab` (`vdkInjCoset_rowPar_le`).
* `vdkInjCoset_rowMap_unimodular`: every value is a unimodular row.
* `vdkInjCoset_rowMap_surjective_of_stableRange`: under `sr(R) ≤ r ≤ n`, every unimodular row
  is a value (this is `vdkInjDirect_reach_of_stableRange`).
* `vdkInjCoset_rowMap_injective_iff`: the map is injective **iff Step A** (`rowStab ≤ P`).
* `vdkInjCoset_rowEquiv`: under Step A and `sr(R) ≤ r ≤ n`, the cosets `P \ St_{n+1}(R)` are in
  bijection with the unimodular rows of length `n + 1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
  (projectionMatrix projectionMatrix_mul projectionMatrix_one)
open scoped Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The last row `e_last ᵥ* M_g` of the matrix of `g`. -/
def vdkInjCoset_rowOf (g : St (n + 1) R) : Fin (n + 1) → R :=
  (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) ᵥ* projectionMatrix g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowOf

theorem vdkInjCoset_rowOf_mul (a b : St (n + 1) R) :
    vdkInjCoset_rowOf (a * b) = vdkInjCoset_rowOf a ᵥ* projectionMatrix b := by
  unfold vdkInjCoset_rowOf
  rw [projectionMatrix_mul, Matrix.vecMul_vecMul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowOf_mul

theorem vdkInjCoset_rowOf_one :
    vdkInjCoset_rowOf (1 : St (n + 1) R) = Pi.single (Fin.last n) 1 := by
  unfold vdkInjCoset_rowOf
  rw [projectionMatrix_one, Matrix.vecMul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowOf_one

theorem vdkInjCoset_mem_rowStab_iff_rowOf (g : St (n + 1) R) :
    g ∈ vdkInjCoset_rowStab n R ↔ vdkInjCoset_rowOf g = Pi.single (Fin.last n) 1 :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_mem_rowStab_iff_rowOf

/-- Two elements have the same last row iff they differ on the left by a row stabiliser. -/
theorem vdkInjCoset_rowOf_eq_iff (a b : St (n + 1) R) :
    vdkInjCoset_rowOf a = vdkInjCoset_rowOf b ↔ b * a⁻¹ ∈ vdkInjCoset_rowStab n R := by
  rw [vdkInjCoset_mem_rowStab_iff_rowOf]
  constructor
  · intro h
    rw [vdkInjCoset_rowOf_mul, ← h, ← vdkInjCoset_rowOf_mul, mul_inv_cancel,
      vdkInjCoset_rowOf_one]
  · intro h
    calc vdkInjCoset_rowOf a
        = (Pi.single (Fin.last n) 1 : Fin (n + 1) → R) ᵥ* projectionMatrix a := rfl
      _ = vdkInjCoset_rowOf (b * a⁻¹) ᵥ* projectionMatrix a := by rw [h]
      _ = vdkInjCoset_rowOf b := by rw [← vdkInjCoset_rowOf_mul, inv_mul_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowOf_eq_iff

/-- Every last row `e_last ᵥ* M_g` is unimodular: pair it with the last column of `M_{g⁻¹}`. -/
theorem vdkInjCoset_rowOf_unimodular (g : St (n + 1) R) :
    vdkStab_IsUnimodular (vdkInjCoset_rowOf g) := by
  refine ⟨projectionMatrix g⁻¹ *ᵥ (Pi.single (Fin.last n) 1 : Fin (n + 1) → R), ?_⟩
  show vdkInjCoset_rowOf g ⬝ᵥ
    (projectionMatrix g⁻¹ *ᵥ (Pi.single (Fin.last n) 1 : Fin (n + 1) → R)) = 1
  rw [Matrix.dotProduct_mulVec, ← vdkInjCoset_rowOf_mul, mul_inv_cancel, vdkInjCoset_rowOf_one,
    single_dotProduct, one_mul, Pi.single_eq_same]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowOf_unimodular

/-- The last row of a coset `P g`: `P g ↦ e_last ᵥ* M_g`. -/
def vdkInjCoset_rowMap : VdKRowCoset n R → Fin (n + 1) → R :=
  Quotient.lift vdkInjCoset_rowOf fun a b hab =>
    (vdkInjCoset_rowOf_eq_iff a b).mpr
      (vdkInjCoset_rowPar_le (QuotientGroup.rightRel_apply.mp hab))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowMap

theorem vdkInjCoset_rowMap_mk (g : St (n + 1) R) :
    vdkInjCoset_rowMap (Quotient.mk (QuotientGroup.rightRel (vdkRowParSubgroup n R)) g) =
      vdkInjCoset_rowOf g :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowMap_mk

theorem vdkInjCoset_rowMap_unimodular (ξ : VdKRowCoset n R) :
    vdkStab_IsUnimodular (vdkInjCoset_rowMap ξ) := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep ξ
  exact vdkInjCoset_rowOf_unimodular g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowMap_unimodular

/-- **Transitivity on cosets**: under `sr(R) ≤ r ≤ n`, every unimodular row is a coset's row. -/
theorem vdkInjCoset_rowMap_surjective_of_stableRange {r : ℕ} (hsr : vdkStab_StableRangeLE R r)
    (hn : r ≤ n) (u : Fin (n + 1) → R) (hu : vdkStab_IsUnimodular u) :
    ∃ ξ : VdKRowCoset n R, vdkInjCoset_rowMap ξ = u := by
  obtain ⟨g, hg⟩ := vdkInjDirect_reach_of_stableRange hsr hn u hu
  exact ⟨Quotient.mk (QuotientGroup.rightRel (vdkRowParSubgroup n R)) g, hg⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowMap_surjective_of_stableRange

/-- **The coset-to-row map is injective iff Step A** (`rowStab ≤ P`). -/
theorem vdkInjCoset_rowMap_injective_iff :
    Function.Injective (vdkInjCoset_rowMap (n := n) (R := R)) ↔ vdkInjCoset_RowStabAt n R := by
  constructor
  · intro hinj g hg
    have h1 : vdkInjCoset_rowMap
        (Quotient.mk (QuotientGroup.rightRel (vdkRowParSubgroup n R)) g) =
          vdkInjCoset_rowMap (Quotient.mk (QuotientGroup.rightRel (vdkRowParSubgroup n R)) 1) := by
      rw [vdkInjCoset_rowMap_mk, vdkInjCoset_rowMap_mk, vdkInjCoset_rowOf_one]
      exact (vdkInjCoset_mem_rowStab_iff_rowOf g).mp hg
    have h2 := QuotientGroup.rightRel_apply.mp (Quotient.eq.mp (hinj h1))
    rw [one_mul] at h2
    have h3 := (vdkRowParSubgroup n R).inv_mem h2
    rwa [inv_inv] at h3
  · intro h ξ ξ' hξ
    obtain ⟨a, rfl⟩ := Quotient.exists_rep ξ
    obtain ⟨b, rfl⟩ := Quotient.exists_rep ξ'
    rw [vdkInjCoset_rowMap_mk, vdkInjCoset_rowMap_mk] at hξ
    exact Quotient.eq.mpr (QuotientGroup.rightRel_apply.mpr (h ((vdkInjCoset_rowOf_eq_iff a b).mp hξ)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowMap_injective_iff

/-- **Orbit–stabiliser under Step A**: for `sr(R) ≤ r ≤ n`, Step A identifies the cosets
`P \ St_{n+1}(R)` with the unimodular rows of length `n + 1`. -/
noncomputable def vdkInjCoset_rowEquiv {r : ℕ} (hsr : vdkStab_StableRangeLE R r) (hn : r ≤ n)
    (h : vdkInjCoset_RowStabAt n R) :
    VdKRowCoset n R ≃ {u : Fin (n + 1) → R // vdkStab_IsUnimodular u} :=
  Equiv.ofBijective (fun ξ => ⟨vdkInjCoset_rowMap ξ, vdkInjCoset_rowMap_unimodular ξ⟩)
    ⟨fun _ _ hab => vdkInjCoset_rowMap_injective_iff.mpr h (congrArg Subtype.val hab),
      fun u => by
        obtain ⟨ξ, hξ⟩ := vdkInjCoset_rowMap_surjective_of_stableRange hsr hn u.1 u.2
        exact ⟨ξ, Subtype.ext hξ⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowEquiv

end GroupApproximation.BooneHigman.Metabelian.ElemFP
