import GroupApproximation.Higman.OmegaTowerStages

/-!
# The slim second stage of the omega tower

This module builds `Π' = Σ' ∗_L a`, the centralizer extension used for the
normal-form computation.  It proves the second defining relation of
`Omega.Tower`: conjugating the new stable letter `a` by `g_β` agrees with
conjugating it by `b_β`.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

/-- The copy of `b_β` in the slim first stage. -/
noncomputable def slimBaseCode (m : ℕ) (β : E) : Cent3 (rowOut m) :=
  emb3 (rowOut m) (Row.basisHom (elt β))

/-- The copy of `g_β` in the slim first stage. -/
noncomputable def slimGenCode (m : ℕ) (β : E) : Cent3 (rowOut m) :=
  genHom (rowOut m) (aElt β)

/-- `g_β b_β⁻¹`, the family centralized at the second stage. -/
noncomputable def slimLinkElem (m : ℕ) (β : E) : Cent3 (rowOut m) :=
  slimGenCode m β * (slimBaseCode m β)⁻¹

/-- Mikaelian's `L` in the slim first stage. -/
noncomputable def slimLink (m : ℕ) : Subgroup (Cent3 (rowOut m)) :=
  Subgroup.closure (slimLinkElem m '' blockSet m)

theorem slimLinkElem_mem {m : ℕ} {β : E} (hβ : β ∈ blockSet m) :
    slimLinkElem m β ∈ slimLink m :=
  Subgroup.subset_closure ⟨β, hβ, rfl⟩

/-- Mikaelian's slim second stage `Π' = Σ' ∗_L a`. -/
abbrev SlimPi (m : ℕ) : Type := CentHNN (slimLink m)

/-- The first-stage base in the slim second stage. -/
noncomputable def slimPiOf (m : ℕ) : Cent3 (rowOut m) →* SlimPi m :=
  (of : Cent3 (rowOut m) →* SlimPi m)

/-- The row carrier in the slim second stage. -/
noncomputable def slimPiRowEmb (m : ℕ) : Row.F₀ →* SlimPi m :=
  (slimPiOf m).comp (emb3 (rowOut m))

/-- The prospective `F₃` embedding: `a` is the new stable letter while `b,c`
come from the old row carrier.  Its injectivity is the next Britton obligation;
the homomorphism and all three generator computations are unconditional. -/
noncomputable def slimPiF3Hom (m : ℕ) : F₃ →* SlimPi m :=
  FreeGroup.lift fun i : Fin 3 =>
    if i = 0 then (t : SlimPi m)
    else if i = 1 then slimPiRowEmb m Row.b
    else slimPiRowEmb m Row.c

@[simp] theorem slimPiF3Hom_a (m : ℕ) :
    slimPiF3Hom m a = (t : SlimPi m) := by
  simp [slimPiF3Hom, a]

@[simp] theorem slimPiF3Hom_b (m : ℕ) :
    slimPiF3Hom m b = slimPiRowEmb m Row.b := by
  simp [slimPiF3Hom, b]

@[simp] theorem slimPiF3Hom_c (m : ℕ) :
    slimPiF3Hom m c = slimPiRowEmb m Row.c := by
  simp [slimPiF3Hom, c]

theorem slimPiF3Hom_rowElt (m : ℕ) (i : ℤ) :
    slimPiF3Hom m (rowElt i) = slimPiRowEmb m (Row.row i) := by
  unfold rowElt Row.row
  rw [map_mul, map_mul, map_zpow, map_zpow, slimPiF3Hom_b, slimPiF3Hom_c,
    map_mul, map_mul, map_zpow, map_zpow]

theorem slimPiF3Hom_comp_rowHom (m : ℕ) :
    (slimPiF3Hom m).comp rowHom = (slimPiRowEmb m).comp Row.basisHom := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, rowHom_of, Row.basisHom_of,
    slimPiF3Hom_rowElt]

theorem slimPiF3Hom_bElt (m : ℕ) (β : E) :
    slimPiF3Hom m (bElt β) = slimPiOf m (slimBaseCode m β) := by
  unfold bElt slimBaseCode slimPiOf
  exact congrArg (fun f : FreeGroup ℤ →* SlimPi m => f (elt β))
    (slimPiF3Hom_comp_rowHom m)

/-- **The slim second-stage relation.**  Since the new `a` centralizes
`g_β b_β⁻¹`, its conjugates by `g_β` and `b_β` agree. -/
theorem slim_conj_gen (m : ℕ) (β : E) (hβ : β ∈ blockSet m) :
    (slimPiOf m (slimGenCode m β))⁻¹ * slimPiF3Hom m a *
        slimPiOf m (slimGenCode m β) = slimPiF3Hom m (aElt β) := by
  let A : SlimPi m := t
  let G : SlimPi m := slimPiOf m (slimGenCode m β)
  let B : SlimPi m := slimPiOf m (slimBaseCode m β)
  have hz : slimPiOf m (slimLinkElem m β) = G * B⁻¹ := by
    simp only [slimPiOf, slimLinkElem, G, B, map_mul, map_inv]
  have hc : Commute A (G * B⁻¹) := by
    apply commute_of_conj_eq
    rw [← hz]
    exact conj_eq_self_of_mem (slimLink m) (slimLinkElem_mem hβ)
  have hconj : G⁻¹ * A * G = B⁻¹ * A * B := by
    calc
      G⁻¹ * A * G = G⁻¹ * (A * (G * B⁻¹)) * B := by group
      _ = G⁻¹ * ((G * B⁻¹) * A) * B := by rw [hc.eq]
      _ = B⁻¹ * A * B := by group
  change G⁻¹ * A * G = slimPiF3Hom m (aElt β)
  rw [hconj]
  unfold aElt
  rw [map_mul, map_mul, map_inv, slimPiF3Hom_bElt, slimPiF3Hom_a]

end Omega
end Higman
end GroupApproximation
