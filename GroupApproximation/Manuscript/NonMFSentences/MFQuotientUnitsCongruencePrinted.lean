import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsOffLastCorner
import GroupApproximation.Manuscript.NonMFSentences.MFQuotientUnitsSteinberg
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:mf-quotient-units`: "Hence `u ≡ v` modulo `N`", along the printed route

`non_mf_groups_exist.tex`, proof of Theorem `thm:mf-quotient-units` (tex 1277–1288):

> Let `u ∈ ker κ` and write `u = gvh` as in (a).  The elementary matrices with `i, j ≤ m-1`
> form `EL_{m-1}(T)` inside `(1-e_m)R(1-e_m) ≅ M_{m-1}(T)`, so they lie in `N` by
> `eq:corner-units`; for distinct `i, j ≤ m-1`, `e_{im}(x) = [e_{ij}(1), e_{jm}(x)]`,
> `e_{mj}(x) = [e_{mi}(x), e_{ij}(1)]` are products of an element of `EL_{m-1}(T)` and a
> conjugate of its inverse, so they lie in the normal subgroup `N` as well.  Hence `u ≡ v`
> modulo `N`, and `κ(v) = κ(u) = 0` because `N ≤ ker κ`.

`manuscriptSentence_congruenceModRadical` assembles the printed argument for an arbitrary
item-(a) decomposition (no block is required to be equivalent to `1`): the off-last roots lie
in `N` by `MFQuotientUnitsOffLastCorner.manuscriptSentence_offLastCorner`; a root with one
index `m` is one of the two displays (`MFQuotientUnitsSteinberg.lastColumnDisplay`,
`lastRowDisplay`, with a third block off `m`); so every elementary matrix of the item-(a)
matrix ring lies in `N`, `u = gvh` gives `u v⁻¹ = g (v h v⁻¹) ∈ N`, and `N ≤ ker κ` gives
`κ(v) = κ(u) = 0`.
-/

namespace GroupApproximation
namespace MFQuotientUnitsCongruencePrinted

open MFQuotientUnits MFQuotientUnitsSteinberg

/-- **Printed (tex 1277–1288), the conclusion "Hence `u ≡ v` modulo `N`, and
`κ(v) = κ(u) = 0`".**  For an item-(a) decomposition (`m + 1` blocks, `m ≥ 3`) of a countable
purely infinite simple ring, every factorization `u = gvh` with `g, h` products of elementary
matrices of the item-(a) matrix ring gives `u v⁻¹ ∈ N`; and if `κ(u) = 0` for a homomorphism
`κ` to a countable abelian group, then `κ(v) = 0`. -/
def PrintedCongruenceModRadical : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ (m : ℕ), 3 ≤ m → ∀ (e : Fin (m + 1) → R) (hidem : ∀ i, IsIdempotentElem (e i)),
      (∀ i j : Fin (m + 1), i ≠ j → e i * e j = 0) → (∑ i, e i = 1) →
      ∀ i₀ last : Fin (m + 1), i₀ ≠ last →
        (∀ i j : Fin (m + 1), i ≠ last → j ≠ last → IsEquivalentIdempotent R (e i) (e j)) →
        ∀ (f : R), IsIdempotentElem f → IdempotentLE f (e i₀) →
          IsEquivalentIdempotent R (e last) f →
          ∀ (A : Type) [CommGroup A] [Countable A] (κ : Rˣ →* A) (u v : Rˣ),
            FactorsThrough (peirceElementarySubgroup e) u v → κ u = 1 →
              u * v⁻¹ ∈ mfHomKernel Rˣ ∧ κ v = 1

theorem manuscriptSentence_congruenceModRadical : PrintedCongruenceModRadical := by
  intro R _ _ hR m hm e hidem horth hsum i₀ last hne hpair f hfi hfle hlast A _ _ κ u v
    hfac hκ
  have hEL : OffLastRootsIn (mfHomKernel Rˣ) e last := by
    obtain ⟨P, hP, θ, -, hroots⟩ :=
      MFQuotientUnitsOffLastCorner.manuscriptSentence_offLastCorner R hR m hm e hidem horth
        hsum i₀ last hne hpair f hfi hfle hlast
    intro p q hpq hpl hql a hpa haq g hg
    obtain ⟨B, -, -, hmem⟩ := hroots p q hpq hpl hql a hpa haq g hg
    exact hmem
  have hle : peirceElementarySubgroup e ≤ mfHomKernel Rˣ := by
    rw [peirceElementarySubgroup, Subgroup.closure_le]
    rintro w ⟨i, j, x, hij, hix, hxj, hw⟩
    by_cases hil : i = last
    · have hjl : j ≠ last := fun h => hij (hil.trans h.symm)
      rw [hil] at hix
      obtain ⟨k, hkj, hkl⟩ := exists_ne_two (by omega : 3 ≤ m + 1) j last
      obtain ⟨g, h, -, -, -, -, -, hmem⟩ :=
        lastRowDisplay (mfHomKernel Rˣ) hidem horth hkj hkl hjl (hpair k j hkl hjl) hEL hix
          hxj w hw
      exact hmem
    · by_cases hjl : j = last
      · rw [hjl] at hxj
        obtain ⟨k, hki, hkl⟩ := exists_ne_two (by omega : 3 ≤ m + 1) i last
        obtain ⟨g, h, -, -, -, -, -, hmem⟩ :=
          lastColumnDisplay (mfHomKernel Rˣ) hidem horth (Ne.symm hki) hil hkl
            (hpair i k hil hkl) hEL hix hxj w hw
        exact hmem
      · exact hEL i j hij hil hjl x hix hxj w hw
  obtain ⟨g, h, hg, hh, huvh⟩ := hfac
  have hsplit : u * v⁻¹ = g * (v * h * v⁻¹) := by rw [huvh]; group
  have hmem : u * v⁻¹ ∈ mfHomKernel Rˣ := by
    rw [hsplit]
    exact (mfHomKernel Rˣ).mul_mem (hle hg) ((mfHomKernel_normal Rˣ).conj_mem _ (hle hh) v)
  refine ⟨hmem, ?_⟩
  have hk : κ (u * v⁻¹) = 1 :=
    MFQuotientUnitsSentences.manuscriptSentence_radicalLeKerKappa κ hmem
  rw [map_mul, hκ, one_mul, map_inv, inv_eq_one] at hk
  exact hk

end MFQuotientUnitsCongruencePrinted
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsCongruencePrinted.manuscriptSentence_congruenceModRadical
