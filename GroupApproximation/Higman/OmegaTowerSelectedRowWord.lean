import GroupApproximation.Higman.OmegaTowerSelectedEndpointTags

/-!
# The selected signed spelling in the row coordinate

The final four-case classifier also uses the exact `K`-valued row equation.
This file computes that homomorphism on an arbitrary raw signed spelling and
records that zero-only stretches contribute the identity.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

@[simp] theorem bK_zero : bK (0 : E) = 1 := by
  apply Subtype.ext
  exact bElt_zero

noncomputable def selectedRowLetter
    {m : ℕ} {B : Set E} (p : SelectedBlock m B × Bool) : ↥Conj.K :=
  if p.2 then (bK (p.1 : E))⁻¹ else bK (p.1 : E)

@[simp] theorem selectedRowInvHom_of
    (m : ℕ) (B : Set E) (beta : SelectedBlock m B) :
    selectedRowInvHom m B (FreeGroup.of beta) = (bK (beta : E))⁻¹ := by
  apply Subtype.ext
  simp [selectedRowInvHom, blockKInvHom, selectedBlockIncl, blockToK]

theorem selectedRowInvHom_mk
    (m : ℕ) (B : Set E) (L : List (SelectedBlock m B × Bool)) :
    selectedRowInvHom m B (FreeGroup.mk L) =
      (L.map selectedRowLetter).prod := by
  induction L with
  | nil => simp
  | cons p L ih =>
      have hmk : FreeGroup.mk (p :: L) = FreeGroup.mk [p] * FreeGroup.mk L := by
        rw [FreeGroup.mul_mk]
      rcases p with ⟨beta, s⟩
      cases s <;>
        simp [hmk, ih, selectedRowLetter, selectedRowInvHom_of]

theorem selectedRowLetter_eq_one_of_zero
    {m : ℕ} {B : Set E} {p : SelectedBlock m B × Bool}
    (hp : (p.1 : E) = 0) : selectedRowLetter p = 1 := by
  cases p.2 <;> simp [selectedRowLetter, hp]

theorem selectedRowLetters_prod_eq_one_of_allZero
    {m : ℕ} {B : Set E} {L : List (SelectedBlock m B × Bool)}
    (hL : AllSelectedZero L) : (L.map selectedRowLetter).prod = 1 := by
  induction L with
  | nil => simp
  | cons p L ih =>
      rw [List.map_cons, List.prod_cons, selectedRowLetter_eq_one_of_zero (hL p (by simp))]
      exact ih fun q hq => hL q (by simp [hq])

theorem selectedRowInvHom_eq_one_of_toWord_allZero
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)}
    (hv : AllSelectedZero v.toWord) : selectedRowInvHom m B v = 1 := by
  rw [← FreeGroup.mk_toWord v, selectedRowInvHom_mk,
    selectedRowLetters_prod_eq_one_of_allZero hv]

theorem selectedRowInvHom_eq_letter_of_decomposition
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)}
    {Z₁ Z₂ : List (SelectedBlock m B × Bool)}
    {p : SelectedBlock m B × Bool}
    (hv : v.toWord = Z₁ ++ p :: Z₂)
    (hZ₁ : AllSelectedZero Z₁) (hZ₂ : AllSelectedZero Z₂) :
    selectedRowInvHom m B v = selectedRowLetter p := by
  rw [← FreeGroup.mk_toWord v, selectedRowInvHom_mk, hv,
    List.map_append, List.prod_append, List.map_cons, List.prod_cons,
    selectedRowLetters_prod_eq_one_of_allZero hZ₁,
    selectedRowLetters_prod_eq_one_of_allZero hZ₂]
  simp

theorem selectedRowInvHom_eq_mul_of_pair_decomposition
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)}
    {Z₀ Z₁ Z₂ : List (SelectedBlock m B × Bool)}
    {p q : SelectedBlock m B × Bool}
    (hv : v.toWord = Z₀ ++ p :: (Z₁ ++ q :: Z₂))
    (hZ₀ : AllSelectedZero Z₀) (hZ₁ : AllSelectedZero Z₁)
    (hZ₂ : AllSelectedZero Z₂) :
    selectedRowInvHom m B v = selectedRowLetter p * selectedRowLetter q := by
  rw [← FreeGroup.mk_toWord v, selectedRowInvHom_mk, hv,
    List.map_append, List.prod_append, List.map_cons, List.prod_cons,
    List.map_append, List.prod_append, List.map_cons, List.prod_cons,
    selectedRowLetters_prod_eq_one_of_allZero hZ₀,
    selectedRowLetters_prod_eq_one_of_allZero hZ₁,
    selectedRowLetters_prod_eq_one_of_allZero hZ₂]
  simp

end Omega
end Higman
end GroupApproximation
