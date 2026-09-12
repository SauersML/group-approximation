import GroupApproximation.Algebra.DiscreteStokes
import GroupApproximation.Sofic.GreendlingerIsoperimetric
import Mathlib.GroupTheory.PresentedGroup

/-!
# The discrete integral against algebraic area

`GroupApproximation.SmallCancellationRouter.IsConjugateProduct R n g` says that
`g` is a product of `n` conjugates of members of `R`: the algebraic area of `g`.
If every member of `R` is trivial in `Q` and has length at most `L`, the discrete
integral of `φ dψ` along `g` (`DiscreteStokes.freeSum`) is at most `n L²` in absolute
value, for all functions `φ ψ : Q → ℤ` moving by at most one along each letter.

For a presented group with a linear isoperimetric inequality this gives the
**linear Stokes inequality**: along every closed word `w`, the integral is at most
`K |w| L²`.  Every lower bound for the integral along a loop is then a lower bound
for the loop's length, and this is how algebraic area enters the proof of Gromov's
theorem in `Algebra/LinearIsoperimetricHyperbolic*.lean` without van Kampen
diagrams.
-/

namespace GroupApproximation
namespace DiscreteStokes

open SmallCancellationRouter

universe u v

variable {α : Type u} {Q : Type v} [Group Q]

/-- **Area bounds the integral.**  A product of `n` conjugates of closed members of
`R`, each of length at most `L`, carries an integral of absolute value at most
`n L²`. -/
theorem abs_freeSum_le_of_isConjugateProduct [DecidableEq α] (f : α → Q) {φ ψ : Q → ℤ}
    (hφ : LipschitzOnLetters f φ) (hψ : LipschitzOnLetters f ψ)
    {R : Set (FreeGroup α)} {L : ℕ}
    (hR : ∀ r ∈ R, FreeGroup.lift f r = 1) (hbound : ∀ r ∈ R, FreeGroup.norm r ≤ L) :
    ∀ (n : ℕ) (g : FreeGroup α) (b : Q), IsConjugateProduct R n g →
      |freeSum f φ ψ b g| ≤ (n : ℤ) * (L : ℤ) ^ 2
  | 0, g, b, h => by
      have hg : g = 1 := h
      subst hg
      simp
  | n + 1, g, b, h => by
      obtain ⟨c, s, k, hs, hg, hk⟩ := h
      subst hg
      have hlift : FreeGroup.lift f (c * s * c⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, hR s hs, mul_one, mul_inv_cancel]
      rw [freeSum_mul, freeSum_conj f φ ψ b c s (hR s hs), hlift, mul_one]
      have h1 := abs_le.mp
        (abs_freeSum_le_of_lift_eq_one f hφ hψ (b * FreeGroup.lift f c) s (hR s hs))
      have h2 := abs_le.mp (abs_freeSum_le_of_isConjugateProduct f hφ hψ hR hbound n k b hk)
      have hnormL : (FreeGroup.norm s : ℤ) ≤ L := by exact_mod_cast hbound s hs
      have hnorm : (FreeGroup.norm s : ℤ) ^ 2 ≤ (L : ℤ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hnormL 2
      have hexp : ((n + 1 : ℕ) : ℤ) * (L : ℤ) ^ 2 = (n : ℤ) * (L : ℤ) ^ 2 + (L : ℤ) ^ 2 := by
        push_cast
        ring
      rw [hexp, abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hnorm]

/-- The universal homomorphism to a presented group is the quotient map. -/
theorem lift_of_eq_presentedGroup_mk (R : Set (FreeGroup α)) :
    (FreeGroup.lift fun x => (PresentedGroup.of x : PresentedGroup R)) =
      PresentedGroup.mk R :=
  FreeGroup.ext_hom _ _ fun a => by simp [PresentedGroup.of]

/-- A relator is trivial in the presented group. -/
theorem lift_of_eq_one_of_mem (R : Set (FreeGroup α)) {r : FreeGroup α} (hr : r ∈ R) :
    FreeGroup.lift (fun x => (PresentedGroup.of x : PresentedGroup R)) r = 1 := by
  rw [lift_of_eq_presentedGroup_mk]
  exact (QuotientGroup.eq_one_iff r).mpr (Subgroup.subset_normalClosure hr)

/-- **The linear Stokes inequality for a presented group.**  If `R` has relators
of length at most `L` and a linear isoperimetric inequality at constant `K`, then
along every free element trivial in `PresentedGroup R` the integral of `φ dψ` is at
most `K |g| L²`. -/
theorem abs_freeSum_le_of_linearIsoperimetric [DecidableEq α] {R : Set (FreeGroup α)}
    {K L : ℕ} (hbound : ∀ r ∈ R, FreeGroup.norm r ≤ L) (hiso : LinearIsoperimetric R K)
    {φ ψ : PresentedGroup R → ℤ}
    (hφ : LipschitzOnLetters (fun x => (PresentedGroup.of x : PresentedGroup R)) φ)
    (hψ : LipschitzOnLetters (fun x => (PresentedGroup.of x : PresentedGroup R)) ψ)
    (b : PresentedGroup R) (g : FreeGroup α)
    (hg : FreeGroup.lift (fun x => (PresentedGroup.of x : PresentedGroup R)) g = 1) :
    |freeSum (fun x => (PresentedGroup.of x : PresentedGroup R)) φ ψ b g| ≤
      (K : ℤ) * (FreeGroup.norm g : ℤ) * (L : ℤ) ^ 2 := by
  have hmem : g ∈ Subgroup.normalClosure R := by
    rw [lift_of_eq_presentedGroup_mk] at hg
    exact (QuotientGroup.eq_one_iff g).mp hg
  obtain ⟨n, hn, hprod⟩ := hiso g hmem
  have h := abs_freeSum_le_of_isConjugateProduct
    (fun x => (PresentedGroup.of x : PresentedGroup R)) hφ hψ
    (fun r hr => lift_of_eq_one_of_mem R hr) hbound n g b hprod
  have hn' : (n : ℤ) ≤ (K : ℤ) * (FreeGroup.norm g : ℤ) := by exact_mod_cast hn
  calc |freeSum (fun x => (PresentedGroup.of x : PresentedGroup R)) φ ψ b g|
      ≤ (n : ℤ) * (L : ℤ) ^ 2 := h
    _ ≤ (K : ℤ) * (FreeGroup.norm g : ℤ) * (L : ℤ) ^ 2 :=
        mul_le_mul_of_nonneg_right hn' (sq_nonneg _)

/-- **The linear Stokes inequality along a closed word.** -/
theorem abs_wordSum_le_of_linearIsoperimetric [DecidableEq α] {R : Set (FreeGroup α)}
    {K L : ℕ} (hbound : ∀ r ∈ R, FreeGroup.norm r ≤ L) (hiso : LinearIsoperimetric R K)
    {φ ψ : PresentedGroup R → ℤ}
    (hφ : LipschitzOnLetters (fun x => (PresentedGroup.of x : PresentedGroup R)) φ)
    (hψ : LipschitzOnLetters (fun x => (PresentedGroup.of x : PresentedGroup R)) ψ)
    (b : PresentedGroup R) (w : List (α × Bool))
    (hw : wordVal (fun x => (PresentedGroup.of x : PresentedGroup R)) w = 1) :
    |wordSum (fun x => (PresentedGroup.of x : PresentedGroup R)) φ ψ b w| ≤
      (K : ℤ) * (w.length : ℤ) * (L : ℤ) ^ 2 := by
  have h := abs_freeSum_le_of_linearIsoperimetric hbound hiso hφ hψ b (FreeGroup.mk w)
    (by rw [lift_mk_eq_wordVal]; exact hw)
  rw [freeSum_mk] at h
  have hnorm : (FreeGroup.norm (FreeGroup.mk w) : ℤ) ≤ w.length := by
    exact_mod_cast FreeGroup.norm_mk_le
  calc |wordSum (fun x => (PresentedGroup.of x : PresentedGroup R)) φ ψ b w|
      ≤ (K : ℤ) * (FreeGroup.norm (FreeGroup.mk w) : ℤ) * (L : ℤ) ^ 2 := h
    _ ≤ (K : ℤ) * (w.length : ℤ) * (L : ℤ) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _)

end DiscreteStokes
end GroupApproximation

#audit_axioms GroupApproximation.DiscreteStokes.abs_freeSum_le_of_isConjugateProduct
#audit_axioms GroupApproximation.DiscreteStokes.abs_freeSum_le_of_linearIsoperimetric
#audit_axioms GroupApproximation.DiscreteStokes.abs_wordSum_le_of_linearIsoperimetric
