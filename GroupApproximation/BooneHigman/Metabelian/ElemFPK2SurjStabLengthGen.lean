import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabLengthSet
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability, length reduction: generator induction (lane bh-met-86)

Here `R` is an arbitrary unital ring, and `S = P Y X Y H ⊆ St_{n+1}(R)` is the set
`SurjStabLengthMem` of `ElemFPK2SurjStabLengthSet`.

* `surjStabLength_mem_mul_x`: if `S` is closed under right multiplication by every
  single-entry last-column root `x_{i,L}(a) = padCol (e_i a)`, then it is closed under right
  multiplication by every Steinberg generator `x_{ij}(b)` of `St_{n+1}`.  A generator with
  `i, j < L` is `stab x_{ij}(b)` (`stab_x`), one with `j = L` is `padCol (e_i b)`
  (`padCol_single`), and one with `i = L` is `padRow (e_j b)` (`padRow_single`).  The last two
  are absorbed by `S` (`surjStabLength_mem_mul_stab`, `surjStabLength_mem_mul_padRow`).
* `surjStabLength_mem_all_of_col`: then `S = St_{n+1}(R)`, by closure induction, since `1 ∈ S`
  and inverses of generators are generators (`x_neg`).
* `surjStabLength_mem_mul_padCol_of_word`: closure under right multiplication by `padCol u`
  follows from `Y X Y X ⊆ S`.  Indeed
  `(H X · Y X Y · stab g₂) · padCol u = H X · (Y X Y · padCol (g₂ u)) · stab g₂`
  (`stab_conj_padCol`), and `S` absorbs `H X` on the left and `H` on the right.

Truth check.  The generator classification is exhaustive: for `i ≠ j` in `Fin (n+1)`, either
both are `castSucc`, or exactly one of them is `last`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

/-- Closure of `S` under right multiplication by every Steinberg generator, given closure
under the single last-column roots. -/
theorem surjStabLength_mem_mul_x
    (hcol : ∀ (s : St (n + 1) R) (i : Fin n) (a : R), SurjStabLengthMem s →
      SurjStabLengthMem (s * padCol (Pi.single i a)))
    {s : St (n + 1) R} (hs : SurjStabLengthMem s) (i j : Fin (n + 1)) (hij : i ≠ j) (b : R) :
    SurjStabLengthMem (s * x i j hij b) := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · have hij' : i' ≠ j' := fun h => hij (congrArg Fin.castSucc h)
      have e : x i'.castSucc j'.castSucc hij b = stab n R (x i' j' hij' b) :=
        (stab_x i' j' hij' b).symm
      rw [e]
      exact surjStabLength_mem_mul_stab hs _
    · have e : x i'.castSucc (Fin.last n) hij b = padCol (Pi.single i' b) :=
        (padCol_single i' b).symm
      rw [e]
      exact hcol s i' b hs
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · have e : x (Fin.last n) j'.castSucc hij b = padRow (Pi.single j' b) :=
        (padRow_single j' b).symm
      rw [e]
      exact surjStabLength_mem_mul_padRow hs _
    · exact absurd rfl hij

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_mem_mul_x

/-- Right closure of `S` under all of `St_{n+1}(R)`. -/
theorem surjStabLength_mem_mul_of_col
    (hcol : ∀ (s : St (n + 1) R) (i : Fin n) (a : R), SurjStabLengthMem s →
      SurjStabLengthMem (s * padCol (Pi.single i a)))
    (y : St (n + 1) R) : ∀ s : St (n + 1) R, SurjStabLengthMem s →
      SurjStabLengthMem (s * y) := by
  have hg := mem_closure_range_of (R := R) y
  induction hg using Subgroup.closure_induction'' with
  | mem g hx =>
    obtain ⟨⟨i, j, hij, b⟩, rfl⟩ := hx
    exact fun s hs => surjStabLength_mem_mul_x hcol hs i j hij b
  | inv_mem g hx =>
    obtain ⟨⟨i, j, hij, b⟩, rfl⟩ := hx
    intro s hs
    have e := surjStabLength_mem_mul_x hcol hs i j hij (-b)
    rw [GroupApproximation.SteinbergGroup.x_neg] at e
    exact e
  | one =>
    intro s hs
    rw [mul_one]
    exact hs
  | mul g h _ _ hg hh =>
    intro s hs
    rw [← mul_assoc]
    exact hh _ (hg s hs)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_mem_mul_of_col

/-- `S = St_{n+1}(R)`, given closure under the single last-column roots. -/
theorem surjStabLength_mem_all_of_col
    (hcol : ∀ (s : St (n + 1) R) (i : Fin n) (a : R), SurjStabLengthMem s →
      SurjStabLengthMem (s * padCol (Pi.single i a)))
    (y : St (n + 1) R) : SurjStabLengthMem y := by
  have h := surjStabLength_mem_mul_of_col hcol y 1 surjStabLength_mem_one
  rwa [one_mul] at h

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_mem_all_of_col

/-- Right closure of `S` under `padCol u`, given `Y X Y X ⊆ S`. -/
theorem surjStabLength_mem_mul_padCol_of_word
    (hword : ∀ w c w' c' : Fin n → R,
      SurjStabLengthMem (padRow w * padCol c * padRow w' * padCol c'))
    {y : St (n + 1) R} (hy : SurjStabLengthMem y) (u : Fin n → R) :
    SurjStabLengthMem (y * padCol u) := by
  obtain ⟨g₁, g₂, v, w, c, w', rfl⟩ := hy
  have e : stab n R g₂ * padCol u = padCol (padMat g₂ *ᵥ u) * stab n R g₂ := by
    rw [← stab_conj_padCol g₂ u, inv_mul_cancel_right]
  have key : stab n R g₁ * padCol v * padRow w * padCol c * padRow w' * stab n R g₂ *
      padCol u = stab n R g₁ * (padCol v *
        ((padRow w * padCol c * padRow w' * padCol (padMat g₂ *ᵥ u)) * stab n R g₂)) := by
    simp only [mul_assoc, e]
  rw [key]
  exact surjStabLength_mem_stab_mul (surjStabLength_mem_padCol_mul
    (surjStabLength_mem_mul_stab (hword w c w' _) g₂) v) g₁

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_mem_mul_padCol_of_word

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
