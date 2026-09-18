import GroupApproximation.BooneHigman.Metabelian.SuslinR1IntEndpoint
import GroupApproximation.PropertyTT.MatrixElimination
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# R1 over `ℤ[1/m]`: prime avoidance in a unimodular row

Lane `bh-met-91i`, part 1.  No matrices beyond one column operation, no literature input.

* `suslinR1Prime_exists_avoid` (Davis-type prime avoidance, in any commutative ring where
  divisibility is well founded): for `z ≠ 0` and any `x, y` there is `l` such that every
  prime `π ∣ z` with `π ∣ x + y l` divides both `x` and `y`.  Take `l` to be the product of
  the irreducible factors of `z` that do NOT divide `x`.
* `suslinR1Prime_avoidCol`: for `τ` invertible over `A[X]` (`A[X]` nontrivial with well
  founded divisibility, e.g. a Noetherian domain) of size `N ≥ 3`, and any row `r`, one
  elementary column operation `ε` and a column `t` make the ideal of the entries of row `r`
  of `τ ε` outside column `t` contained in NO principal ideal `(π)` with `π` prime.
  (Pick a nonzero entry `v_c`, two further columns `a ≠ b`, and add `l` times column `b` to
  column `a`; a prime containing the other entries divides `v_c` and `v_a + l v_b`, hence
  `v_a` and `v_b`, hence the whole unimodular row.)
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- A non-unit dividing an irreducible element is divisible by it. -/
theorem suslinR1Prime_dvd_of_irreducible {R : Type*} [CommMonoid R] {π w : R}
    (hw : Irreducible w) (hπ : ¬IsUnit π) (h : π ∣ w) : w ∣ π := by
  obtain ⟨u, rfl⟩ := h
  exact (IsUnit.mul_right_dvd (Or.resolve_left (of_irreducible_mul hw) hπ)).2 dvd_rfl

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Prime_dvd_of_irreducible

/-- **Davis-type prime avoidance.**  For `z ≠ 0` there is `l` such that every prime divisor
of `z` that divides `x + y l` divides `x` and `y`. -/
theorem suslinR1Prime_exists_avoid {R : Type*} [CommRing R] [WfDvdMonoid R] {x y z : R}
    (hz : z ≠ 0) :
    ∃ l : R, ∀ π : R, Prime π → π ∣ z → π ∣ x + y * l →
      π ∣ x ∧ π ∣ y := by
  classical
  obtain ⟨f, hirr, hassoc⟩ := WfDvdMonoid.exists_factors z hz
  refine ⟨(f.filter fun w ↦ ¬w ∣ x).prod, fun π hπ hπz hπs ↦ ?_⟩
  obtain ⟨w, hwf, hπw⟩ := hπ.exists_mem_multiset_dvd (hπz.trans hassoc.symm.dvd)
  by_cases hπx : π ∣ x
  · refine ⟨hπx, ?_⟩
    rcases hπ.dvd_or_dvd ((dvd_add_right hπx).mp hπs) with hy | hl
    · exact hy
    · exfalso
      obtain ⟨v, hvf, hπv⟩ := hπ.exists_mem_multiset_dvd hl
      rw [Multiset.mem_filter] at hvf
      exact hvf.2 ((suslinR1Prime_dvd_of_irreducible (hirr v hvf.1) hπ.not_unit hπv).trans hπx)
  · exfalso
    have hwF : w ∈ f.filter fun w ↦ ¬w ∣ x :=
      Multiset.mem_filter.2 ⟨hwf, fun hwx ↦ hπx (hπw.trans hwx)⟩
    exact hπx ((dvd_add_left ((hπw.trans (Multiset.dvd_prod hwF)).mul_left y)).mp hπs)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Prime_exists_avoid

/-- Row `r` of an invertible matrix, paired with column `r` of its inverse, sums to `1`. -/
theorem suslinR1Prime_row_sum {B : Type*} [CommRing B] {N : ℕ}
    (τ : Matrix.GeneralLinearGroup (Fin N) B) (r : Fin N) :
    ∑ j, τ.val r j * (τ⁻¹ : Matrix.GeneralLinearGroup (Fin N) B).val j r = 1 := by
  have h : (τ.val * (τ⁻¹ : Matrix.GeneralLinearGroup (Fin N) B).val) r r = 1 := by
    rw [Units.mul_inv, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Prime_row_sum

/-- No prime divides every entry of a row of an invertible matrix. -/
theorem suslinR1Prime_not_dvd_row {B : Type*} [CommRing B] {N : ℕ}
    (τ : Matrix.GeneralLinearGroup (Fin N) B) (r : Fin N) {π : B} (hπ : Prime π) :
    ¬∀ j, π ∣ τ.val r j := by
  intro h
  apply hπ.not_dvd_one
  rw [← suslinR1Prime_row_sum τ r]
  exact Finset.dvd_sum fun j _ ↦ (h j).mul_right _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Prime_not_dvd_row

/-- Over a nontrivial ring, every row of an invertible matrix has a nonzero entry. -/
theorem suslinR1Prime_exists_ne_zero {B : Type*} [CommRing B] [Nontrivial B] {N : ℕ}
    (τ : Matrix.GeneralLinearGroup (Fin N) B) (r : Fin N) : ∃ j, τ.val r j ≠ 0 := by
  by_contra h
  have h0 : ∀ j, τ.val r j = 0 := fun j ↦ by
    by_contra hj
    exact h ⟨j, hj⟩
  have h1 := suslinR1Prime_row_sum τ r
  simp only [h0, zero_mul, Finset.sum_const_zero] at h1
  exact zero_ne_one h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Prime_exists_ne_zero

/-- **One column operation avoids every principal prime.**  For `τ` invertible of size
`N ≥ 3` over `A[X]` and any row `r`, there are an elementary `ε` and a column `t` such that
the ideal of the entries of row `r` of `τ ε` outside column `t` lies in no `(π)`, `π` prime. -/
theorem suslinR1Prime_avoidCol {A : Type*} [CommRing A] [Nontrivial A]
    [WfDvdMonoid (Polynomial A)] {N : ℕ} (hN : 3 ≤ N)
    (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A)) (r : Fin N) :
    ∃ ε ∈ elementaryGroup (Fin N) (Polynomial A), ∃ t : Fin N,
      ∀ π : Polynomial A, Prime π →
        ¬suslinR1Int_rowIdeal (τ * ε) r t ≤ Ideal.span {π} := by
  obtain ⟨c, hc⟩ := suslinR1Prime_exists_ne_zero τ r
  have hcard : 1 < ((Finset.univ : Finset (Fin N)).erase c).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
  rw [Finset.mem_erase] at ha hb
  obtain ⟨l, hl⟩ := suslinR1Prime_exists_avoid (x := τ.val r a) (y := τ.val r b) hc
  refine ⟨elementaryUnit b a hab.symm l, elementaryUnit_mem b a hab.symm l, b,
    fun π hπ hle ↦ ?_⟩
  have happ : ∀ j, (τ * elementaryUnit b a hab.symm l).val r j =
      if j = a then τ.val r a + τ.val r b * l else τ.val r j := fun j ↦ by
    rw [Units.val_mul]
    exact mul_elementaryUnit_apply τ.val b a hab.symm l r j
  have hdvd : ∀ j, j ≠ b → π ∣ (τ * elementaryUnit b a hab.symm l).val r j := fun j hj ↦
    Ideal.mem_span_singleton.1 (hle (suslinR1Int_entry_mem_rowIdeal _ r hj))
  have hca : c ≠ a := fun h ↦ ha.1 h.symm
  have hcb : c ≠ b := fun h ↦ hb.1 h.symm
  have hπc : π ∣ τ.val r c := by
    have h := hdvd c hcb
    rwa [happ, if_neg hca] at h
  have hπs : π ∣ τ.val r a + τ.val r b * l := by
    have h := hdvd a hab
    rwa [happ, if_pos rfl] at h
  obtain ⟨hπa, hπb⟩ := hl π hπ hπc hπs
  refine suslinR1Prime_not_dvd_row τ r hπ fun j ↦ ?_
  by_cases hja : j = a
  · rw [hja]
    exact hπa
  · by_cases hjb : j = b
    · rw [hjb]
      exact hπb
    · have h := hdvd j hjb
      rwa [happ, if_neg hja] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR1Prime_avoidCol

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
