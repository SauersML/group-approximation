import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPPRel
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStFourFPStCentral
import GroupApproximation.Meta.AxiomGuard

/-!
# `St_4(ℤ[1/m])` is a retract of `P m` (bh-met-91m)

`φ : P m → St_4(ℤ[1/m])` sends `Y α ↦ x_α(1)` and `T s ↦ H_s(m)`.  The integral relators hold
since `St_4(ℤ) → St_4(ℤ[1/m])` is a homomorphism, the scaling relators by
`czStFourFP_H_conj`, and the centrality relators by `czStFourFP_H_central`.  With the section
`ψ` of `ElemFPCharZeroStFourFPPRel`, `φ ∘ ψ = id` (`czStFourFP_phi_psi`), so `St_4(ℤ[1/m])` is
finitely presented (`czStFourFP_stFour_of_pos`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped commutatorElement

theorem czStFourFP_hthird : ∀ a b : Fin 4, ∃ k, k ≠ a ∧ k ≠ b := by decide

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_hthird

/-- Images of the generators: `Y α ↦ x_α(1)`, `T s ↦ H_s(m)`. -/
noncomputable def czStFourFP_phiGen (m : ℕ) :
    czStFourFP_Gen → SteinbergGroup (Fin 4) (czStFourFP_R m) :=
  Sum.elim (fun α => SteinbergGroup.x α.1.1 α.1.2 α.2 1)
    (fun s => czStFourFP_H s.1.1 s.1.2 s.2 (czStFourFP_u m))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_phiGen

theorem czStFourFP_lift_inl (m : ℕ) :
    (FreeGroup.lift (czStFourFP_phiGen m)).comp czStFourFP_inl =
      FreeGroup.lift (fun α : czStFourFP_Root =>
        SteinbergGroup.x α.1.1 α.1.2 α.2 (1 : czStFourFP_R m)) :=
  FreeGroup.ext_hom _ _ fun α => by
    rw [MonoidHom.comp_apply, czStFourFP_inl, FreeGroup.map.of, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of]
    rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_lift_inl

/-- The integral relators. -/
theorem czStFourFP_phi_int (m : ℕ) (w : FreeGroup czStFourFP_Root)
    (hw : w ∈ czSLFourFP_intRels (Fin 4)) :
    FreeGroup.lift (czStFourFP_phiGen m) (czStFourFP_inl w) = 1 := by
  have hl := DFunLike.congr_fun (czStFourFP_lift_inl m) w
  rw [MonoidHom.comp_apply] at hl
  rw [hl]
  rcases hw with ⟨⟨⟨⟨⟨i, j⟩, hij⟩, ⟨⟨k, l⟩, hkl⟩⟩, hjk, hli⟩, rfl⟩ |
    ⟨⟨⟨i, j, k⟩, hij, hjk, hik⟩, rfl⟩
  · simp only [czSLFourFP_commRel, map_commutatorElement, FreeGroup.lift_apply_of]
    exact (SteinbergGroup.x_commute_of_ne i j k l hij hkl hjk hli
      (1 : czStFourFP_R m) 1).commutator_eq
  · simp only [czSLFourFP_adjRel, map_mul, map_inv, map_commutatorElement,
      FreeGroup.lift_apply_of]
    change ⁅SteinbergGroup.x i j hij (1 : czStFourFP_R m), SteinbergGroup.x j k hjk 1⁆ *
      (SteinbergGroup.x i k hik 1)⁻¹ = 1
    rw [SteinbergGroup.x_commutator i j k hij hjk hik, one_mul, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_phi_int

/-- The scaling relators. -/
theorem czStFourFP_phi_scale (m : ℕ) (s α : czStFourFP_Root) :
    FreeGroup.lift (czStFourFP_phiGen m) (czStFourFP_scaleRel m s α) = 1 := by
  by_cases h : 0 ≤ czStFourFP_chi s.1.1 s.1.2 α.1.1 α.1.2
  · rw [czStFourFP_scaleRel, if_pos h]
    simp only [map_mul, map_inv, map_zpow, FreeGroup.lift_apply_of]
    change czStFourFP_H s.1.1 s.1.2 s.2 (czStFourFP_u m) *
        SteinbergGroup.x α.1.1 α.1.2 α.2 1 *
        (czStFourFP_H s.1.1 s.1.2 s.2 (czStFourFP_u m))⁻¹ *
        (SteinbergGroup.x α.1.1 α.1.2 α.2 1 ^
          ((m : ℤ) ^ (czStFourFP_chi s.1.1 s.1.2 α.1.1 α.1.2).toNat))⁻¹ = 1
    rw [czStFourFP_H_conj czStFourFP_hthird, czStFourFP_x_zpow, czStFourFP_u_zpow m h]
    exact mul_inv_cancel _
  · rw [czStFourFP_scaleRel, if_neg h, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_phi_scale

/-- The centrality relators. -/
theorem czStFourFP_phi_cent (m : ℕ) (s α : czStFourFP_Root) (g : czStFourFP_Gen) :
    FreeGroup.lift (czStFourFP_phiGen m) (czStFourFP_centRel s α g) = 1 := by
  simp only [czStFourFP_centRel, map_commutatorElement, map_mul, map_inv,
    FreeGroup.lift_apply_of]
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (czStFourFP_H_central czStFourFP_hthird s.1.1 s.1.2 α.1.1 α.1.2 s.2 α.2
      (czStFourFP_u m) (czStFourFP_u m) (czStFourFP_phiGen m g)).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_phi_cent

theorem czStFourFP_phi_rels (m : ℕ) :
    ∀ r ∈ czStFourFP_rels m, FreeGroup.lift (czStFourFP_phiGen m) r = 1 := by
  rintro r ((⟨w, hw, rfl⟩ | ⟨⟨s, α⟩, rfl⟩) | ⟨⟨s, α, g⟩, rfl⟩)
  · exact czStFourFP_phi_int m w hw
  · exact czStFourFP_phi_scale m s α
  · exact czStFourFP_phi_cent m s α g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_phi_rels

/-- **The projection** `φ : P m → St_4(ℤ[1/m])`. -/
noncomputable def czStFourFP_phi (m : ℕ) :
    czStFourFP_P m →* SteinbergGroup (Fin 4) (czStFourFP_R m) :=
  PresentedGroup.toGroup (czStFourFP_phi_rels m)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_phi

theorem czStFourFP_phi_Y (m : ℕ) (α : czStFourFP_Root) :
    czStFourFP_phi m (czStFourFP_Y m α) = SteinbergGroup.x α.1.1 α.1.2 α.2 1 :=
  PresentedGroup.toGroup.of (czStFourFP_phi_rels m)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_phi_Y

theorem czStFourFP_phi_T (m : ℕ) (s : czStFourFP_Root) :
    czStFourFP_phi m (czStFourFP_T m s) = czStFourFP_H s.1.1 s.1.2 s.2 (czStFourFP_u m) :=
  PresentedGroup.toGroup.of (czStFourFP_phi_rels m)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_phi_T

/-- `φ (XP_α(r)) = x_α(r)`: write `XP_α(r) = T α⁻ᵏ Y α ⁿ T α ᵏ` with `m ^ (2k) r = n`. -/
theorem czStFourFP_phi_XP (m : ℕ) (hm : 0 < m) (α : czStFourFP_Root) (r : czStFourFP_R m) :
    czStFourFP_phi m (czStFourFP_XP m α r) = SteinbergGroup.x α.1.1 α.1.2 α.2 r := by
  obtain ⟨k, n, h⟩ := czStFourFP_surj m r
  rw [czStFourFP_XP_rep m hm α r k n h, map_mul, map_mul, map_inv, map_pow, map_zpow,
    czStFourFP_phi_T, czStFourFP_phi_Y, czStFourFP_x_zpow, mul_one]
  have e := czStFourFP_conj_pow_iter (f := SteinbergGroup.x α.1.1 α.1.2 α.2)
    (czStFourFP_H_conj czStFourFP_hthird α.1.1 α.1.2 α.2 (czStFourFP_u m) α.1.1 α.1.2 α.2) k r
  rw [czStFourFP_chi_ab α.2, zpow_two, Units.val_mul, czStFourFP_u_val, ← sq, h] at e
  exact czStFourFP_conj_inv_of e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_phi_XP

/-- **Retraction.**  `φ ∘ ψ = id`. -/
theorem czStFourFP_phi_psi (m : ℕ) (hm : 0 < m) (g : SteinbergGroup (Fin 4) (czStFourFP_R m)) :
    czStFourFP_phi m (czStFourFP_psi m hm g) = g := by
  have hc : (czStFourFP_phi m).comp (czStFourFP_psi m hm) = MonoidHom.id _ :=
    PresentedGroup.ext fun gen => by
      obtain ⟨i, j, hij, r⟩ := gen
      rw [MonoidHom.comp_apply, MonoidHom.id_apply]
      exact (congrArg (czStFourFP_phi m) (czStFourFP_psi_x m hm i j hij r)).trans
        (czStFourFP_phi_XP m hm ⟨(i, j), hij⟩ r)
  exact DFunLike.congr_fun hc g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_phi_psi

/-- **`St_4(ℤ[1/m])` is finitely presented** for every `m > 0`. -/
theorem czStFourFP_stFour_of_pos (m : ℕ) (hm : 0 < m) :
    Group.IsFinitelyPresented (SteinbergGroup (Fin 4) (czStFourFP_R m)) :=
  czStFourFP_isFinitelyPresented_of_retract (czStFourFP_phi m) (czStFourFP_psi m hm)
    (czStFourFP_phi_psi m hm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czStFourFP_stFour_of_pos

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
