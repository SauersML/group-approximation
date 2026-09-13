import GroupApproximation.Pestov91.LEF
import Mathlib.Algebra.SkewMonoidAlgebra.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Crossed products by `ℤ` with periodic models are LEF rings

Let `A` be a ring with an action of `ℤ` (written multiplicatively). Suppose that every finite
piece of `A` and of the action can be modelled faithfully on a cycle: for every finite `T ⊆ A`
and every `B` there is a ring homomorphism `D : A →+* (ZMod N → K)` into functions on a cycle
of length `N > 2B` with values in a finite ring `K`, which does not kill nonzero elements of `T`
and intertwines translation by `|i| ≤ B` on `T` with the rotation of the cycle.

Then the crossed product `SkewMonoidAlgebra A (Multiplicative ℤ)` is an LEF ring
(`isLEFRing_skewMonoidAlgebra_of_periodic`). The model sends `single g a` to
`diagonal (D a) * shiftMatrix K N (toAdd g)`, where `shiftMatrix K N i` is the cyclic shift by `i`.
It is additive; it is multiplicative on the given finite set because `D` intertwines the action
with the shift there; and it is injective there because the supports lie in `[-B, B]`, which
embeds in `ZMod N`.
-/

namespace GroupApproximation
namespace Pestov91

open Matrix

/-- The cyclic shift by `i` on `ZMod N`: `shiftMatrix K N i a b = 1` iff `b + i = a`. -/
def shiftMatrix (K : Type*) [Zero K] [One K] (N : ℕ) (i : ℤ) : Matrix (ZMod N) (ZMod N) K :=
  fun a b ↦ if b + (i : ZMod N) = a then 1 else 0

section Shift

variable {K : Type*} [Semiring K] {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem shiftMatrix_apply (i : ℤ) (a b : ZMod N) :
    shiftMatrix K N i a b = if b + (i : ZMod N) = a then 1 else 0 := rfl

omit [NeZero N] in
theorem shiftMatrix_zero : shiftMatrix K N 0 = 1 := by
  ext a b
  rw [shiftMatrix_apply, Int.cast_zero, add_zero, Matrix.one_apply]
  by_cases h : a = b
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem shiftMatrix_add (i j : ℤ) :
    shiftMatrix K N (i + j) = shiftMatrix K N i * shiftMatrix K N j := by
  ext a c
  rw [Matrix.mul_apply, Finset.sum_eq_single (a - (i : ZMod N))]
  · rw [shiftMatrix_apply i a (a - (i : ZMod N)), if_pos (sub_add_cancel a _), one_mul,
      shiftMatrix_apply (i + j) a c, shiftMatrix_apply j (a - (i : ZMod N)) c, Int.cast_add]
    by_cases h : c + ((i : ZMod N) + j) = a
    · rw [if_pos h, if_pos (by linear_combination h)]
    · rw [if_neg h, if_neg (fun h' ↦ h (by linear_combination h'))]
  · intro b _ hb
    rw [shiftMatrix_apply i a b, if_neg (fun h ↦ hb (by linear_combination h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Covariance: `P^i D(d) = D(d(· - i)) P^i`. -/
theorem shiftMatrix_mul_diagonal (i : ℤ) (d : ZMod N → K) :
    shiftMatrix K N i * diagonal d = diagonal (fun a ↦ d (a - (i : ZMod N))) * shiftMatrix K N i := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, shiftMatrix_apply i a b]
  by_cases h : b + (i : ZMod N) = a
  · rw [if_pos h, one_mul, mul_one]
    show d b = d (a - (i : ZMod N))
    rw [← h, add_sub_cancel_right]
  · rw [if_neg h, zero_mul, mul_zero]

theorem diagonal_mul_shiftMatrix_apply (i : ℤ) (d : ZMod N → K) (a b : ZMod N) :
    (diagonal d * shiftMatrix K N i) a b = if b + (i : ZMod N) = a then d a else 0 := by
  rw [Matrix.diagonal_mul, shiftMatrix_apply i a b]
  by_cases h : b + (i : ZMod N) = a
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- A sum `∑_{j ∈ S} D(d_j) P^{e j}` determines each `d_j` when `j ↦ e j` is injective mod `N`. -/
theorem eq_zero_of_sum_diagonal_mul_shiftMatrix_eq_zero {ι : Type*} (S : Finset ι) (e : ι → ℤ)
    (hS : Set.InjOn (fun j ↦ (e j : ZMod N)) (S : Set ι)) (d : ι → ZMod N → K)
    (h : ∑ j ∈ S, diagonal (d j) * shiftMatrix K N (e j) = 0) : ∀ j ∈ S, d j = 0 := by
  intro j₀ hj₀
  funext a
  have hentry : (∑ j ∈ S, diagonal (d j) * shiftMatrix K N (e j)) a (a - (e j₀ : ZMod N)) = 0 := by
    rw [h, Matrix.zero_apply]
  rw [Matrix.sum_apply, Finset.sum_eq_single j₀, diagonal_mul_shiftMatrix_apply,
    if_pos (sub_add_cancel a _)] at hentry
  · exact hentry
  · intro j hj hne
    rw [diagonal_mul_shiftMatrix_apply, if_neg]
    intro hc
    exact hne (hS hj hj₀ (by
      show (e j : ZMod N) = e j₀
      linear_combination hc))
  · intro h'
    exact absurd hj₀ h'

omit [NeZero N] in
theorem intCast_zmod_inj {B : ℕ} (hB : 2 * B < N) {a b : ℤ} (ha : |a| ≤ B) (hb : |b| ≤ B)
    (hab : (a : ZMod N) = b) : a = b := by
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hcast : ((a + B : ℤ) : ZMod N) = ((b + B : ℤ) : ZMod N) := by
    rw [Int.cast_add, Int.cast_add, hab]
  have hmod := (ZMod.intCast_eq_intCast_iff' _ _ N).mp hcast
  have h1 : (a + B) % (N : ℤ) = a + B := Int.emod_eq_of_lt (by omega) (by omega)
  have h2 : (b + B) % (N : ℤ) = b + B := Int.emod_eq_of_lt (by omega) (by omega)
  rw [h1, h2] at hmod
  omega

end Shift

section Model

variable {A : Type*} [Ring A] {K : Type*} [Ring K] {N : ℕ} [NeZero N]

/-- The periodic model of the crossed product: `single g a ↦ diagonal (D a) * P^{toAdd g}`. -/
noncomputable def periodicModel (D : A →+* (ZMod N → K)) :
    SkewMonoidAlgebra A (Multiplicative ℤ) →+ Matrix (ZMod N) (ZMod N) K :=
  SkewMonoidAlgebra.liftNC ((Matrix.diagonalAddMonoidHom (ZMod N) K).comp D.toAddMonoidHom)
    fun g ↦ shiftMatrix K N (Multiplicative.toAdd g)

theorem periodicModel_single (D : A →+* (ZMod N → K)) (g : Multiplicative ℤ) (a : A) :
    periodicModel D (SkewMonoidAlgebra.single g a) =
      diagonal (D a) * shiftMatrix K N (Multiplicative.toAdd g) :=
  SkewMonoidAlgebra.liftNC_single _ _ _ _

theorem periodicModel_eq_sum (D : A →+* (ZMod N → K)) (x : SkewMonoidAlgebra A (Multiplicative ℤ)) :
    periodicModel D x = ∑ g ∈ x.support,
      diagonal (D (x.coeff g)) * shiftMatrix K N (Multiplicative.toAdd g) := by
  have hx : x = ∑ g ∈ x.support, SkewMonoidAlgebra.single g (x.coeff g) :=
    (SkewMonoidAlgebra.sum_single x).symm.trans (SkewMonoidAlgebra.sum_def' x SkewMonoidAlgebra.single)
  rw [congrArg (periodicModel D) hx, map_sum]
  exact Finset.sum_congr rfl fun g _ ↦ periodicModel_single D g (x.coeff g)

theorem periodicModel_one (D : A →+* (ZMod N → K)) : periodicModel D 1 = 1 := by
  have h1 : diagonal (1 : ZMod N → K) = 1 := Matrix.diagonal_one
  have h0 : shiftMatrix K N (Multiplicative.toAdd (1 : Multiplicative ℤ)) = 1 := shiftMatrix_zero
  rw [SkewMonoidAlgebra.one_def, periodicModel_single, map_one, h1, h0, one_mul]

theorem eq_of_periodicModel_eq (D : A →+* (ZMod N → K)) {B : ℕ} (hB : 2 * B < N)
    {x y : SkewMonoidAlgebra A (Multiplicative ℤ)}
    (hsx : ∀ g ∈ x.support, |Multiplicative.toAdd g| ≤ B)
    (hsy : ∀ g ∈ y.support, |Multiplicative.toAdd g| ≤ B)
    (hD : ∀ g ∈ x.support ∪ y.support, D (x.coeff g - y.coeff g) = 0 → x.coeff g = y.coeff g)
    (hxy : periodicModel D x = periodicModel D y) : x = y := by
  have hc : ∀ g, (x - y).coeff g = x.coeff g - y.coeff g := fun g ↦ by
    rw [SkewMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  have hsupp : ∀ g ∈ (x - y).support, g ∈ x.support ∪ y.support := by
    intro g hg
    rw [SkewMonoidAlgebra.mem_support_iff, hc] at hg
    rw [Finset.mem_union, SkewMonoidAlgebra.mem_support_iff, SkewMonoidAlgebra.mem_support_iff]
    by_contra hn
    push Not at hn
    exact hg (by rw [hn.1, hn.2, sub_zero])
  have hbd : ∀ g ∈ (x - y).support, |Multiplicative.toAdd g| ≤ B := fun g hg ↦
    (Finset.mem_union.mp (hsupp g hg)).elim (hsx g) (hsy g)
  have hinj : Set.InjOn (fun g : Multiplicative ℤ ↦ ((Multiplicative.toAdd g : ℤ) : ZMod N))
      ((x - y).support : Set (Multiplicative ℤ)) :=
    fun a ha b hb hab ↦ intCast_zmod_inj hB (hbd a ha) (hbd b hb) hab
  have hsub : periodicModel D (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [periodicModel_eq_sum] at hsub
  have hz := eq_zero_of_sum_diagonal_mul_shiftMatrix_eq_zero (x - y).support
    (fun g ↦ Multiplicative.toAdd g) hinj (fun g ↦ D ((x - y).coeff g)) hsub
  refine SkewMonoidAlgebra.ext fun g ↦ ?_
  by_contra hne
  have hg : g ∈ (x - y).support := by
    rw [SkewMonoidAlgebra.mem_support_iff, hc]
    exact sub_ne_zero.mpr hne
  have h0 : D ((x - y).coeff g) = 0 := hz g hg
  rw [hc] at h0
  exact hne (hD g (hsupp g hg) h0)

end Model

section CrossedProduct

variable {A : Type*} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
  {K : Type*} [Ring K] {N : ℕ} [NeZero N]

theorem periodicModel_mul (D : A →+* (ZMod N → K)) (x y : SkewMonoidAlgebra A (Multiplicative ℤ))
    (hcov : ∀ g ∈ x.support, ∀ h ∈ y.support, ∀ n : ZMod N,
      D (g • y.coeff h) n = D (y.coeff h) (n - (Multiplicative.toAdd g : ℤ))) :
    periodicModel D (x * y) = periodicModel D x * periodicModel D y := by
  rw [periodicModel_eq_sum D x, periodicModel_eq_sum D y, Finset.sum_mul, SkewMonoidAlgebra.mul_def,
    SkewMonoidAlgebra.sum_def', map_sum]
  refine Finset.sum_congr rfl fun g hg ↦ ?_
  rw [Finset.mul_sum, SkewMonoidAlgebra.sum_def', map_sum]
  refine Finset.sum_congr rfl fun h hh ↦ ?_
  have hd : (fun a : ZMod N ↦ D (y.coeff h) (a - ((Multiplicative.toAdd g : ℤ) : ZMod N))) =
      D (g • y.coeff h) :=
    funext fun n ↦ (hcov g hg h hh n).symm
  have hcomm : shiftMatrix K N (Multiplicative.toAdd g) * diagonal (D (y.coeff h)) =
      diagonal (D (g • y.coeff h)) * shiftMatrix K N (Multiplicative.toAdd g) := by
    rw [← hd]
    exact shiftMatrix_mul_diagonal (Multiplicative.toAdd g) (D (y.coeff h))
  have hP : shiftMatrix K N (Multiplicative.toAdd (g * h)) =
      shiftMatrix K N (Multiplicative.toAdd g) * shiftMatrix K N (Multiplicative.toAdd h) :=
    shiftMatrix_add (Multiplicative.toAdd g) (Multiplicative.toAdd h)
  have hdiag : diagonal (D (x.coeff g) * D (g • y.coeff h)) =
      diagonal (D (x.coeff g)) * diagonal (D (g • y.coeff h)) :=
    (Matrix.diagonal_mul_diagonal _ _).symm
  rw [periodicModel_single, map_mul D, hdiag, hP]
  calc diagonal (D (x.coeff g)) * diagonal (D (g • y.coeff h)) *
        (shiftMatrix K N (Multiplicative.toAdd g) * shiftMatrix K N (Multiplicative.toAdd h))
      = diagonal (D (x.coeff g)) *
          (diagonal (D (g • y.coeff h)) * shiftMatrix K N (Multiplicative.toAdd g)) *
          shiftMatrix K N (Multiplicative.toAdd h) := by
        simp only [mul_assoc]
    _ = diagonal (D (x.coeff g)) * shiftMatrix K N (Multiplicative.toAdd g) *
          (diagonal (D (y.coeff h)) * shiftMatrix K N (Multiplicative.toAdd h)) := by
        rw [← hcomm]
        simp only [mul_assoc]

/-- **Crossed products with periodic models are LEF rings.** If every finite piece of `A` and of
the `ℤ`-action has a faithful covariant model on a long enough cycle, then
`SkewMonoidAlgebra A (Multiplicative ℤ)` is an LEF ring. -/
theorem isLEFRing_skewMonoidAlgebra_of_periodic
    (hper : ∀ (T : Finset A) (B : ℕ), ∃ (K : Type) (_ : Ring K) (_ : Finite K) (N : ℕ)
      (_ : NeZero N) (D : A →+* (ZMod N → K)), 2 * B < N ∧ (∀ a ∈ T, a ≠ 0 → D a ≠ 0) ∧
      ∀ a ∈ T, ∀ g : Multiplicative ℤ, |Multiplicative.toAdd g| ≤ B → ∀ n : ZMod N,
        D (g • a) n = D a (n - (Multiplicative.toAdd g : ℤ))) :
    IsLEFRing (SkewMonoidAlgebra A (Multiplicative ℤ)) := by
  classical
  intro t
  obtain ⟨B, hbd⟩ : ∃ B : ℕ, ∀ x ∈ t, ∀ g ∈ x.support, |Multiplicative.toAdd g| ≤ B :=
    ⟨(t.biUnion SkewMonoidAlgebra.support).sup fun g ↦ (Multiplicative.toAdd g).natAbs,
      fun x hx g hg ↦ by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast Finset.le_sup (f := fun g : Multiplicative ℤ ↦ (Multiplicative.toAdd g).natAbs)
          (Finset.mem_biUnion.mpr ⟨x, hx, hg⟩)⟩
  obtain ⟨T, hTdiff, hTcoeff⟩ : ∃ T : Finset A,
      (∀ x ∈ t, ∀ y ∈ t, ∀ g ∈ x.support ∪ y.support, x.coeff g - y.coeff g ∈ T) ∧
      (∀ x ∈ t, ∀ g ∈ x.support, x.coeff g ∈ T) :=
    ⟨(t ×ˢ t).biUnion (fun p ↦ (p.1.support ∪ p.2.support).image fun g ↦ p.1.coeff g - p.2.coeff g)
        ∪ t.biUnion (fun x ↦ x.support.image x.coeff),
      fun x hx y hy g hg ↦ Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, Finset.mem_image.mpr ⟨g, hg, rfl⟩⟩),
      fun x hx g hg ↦ Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨x, hx, Finset.mem_image.mpr ⟨g, hg, rfl⟩⟩)⟩
  obtain ⟨K, _, _, N, _, D, hN, hnz, hcov⟩ := hper T B
  refine ⟨Matrix (ZMod N) (ZMod N) K, inferInstance, inferInstance, periodicModel D, ?_,
    map_zero _, periodicModel_one D, fun x hx y hy ↦ ⟨map_add _ x y, periodicModel_mul D x y
      fun g hg h hh n ↦ hcov _ (hTcoeff y hy h hh) g (hbd x hx g hg) n⟩⟩
  intro x hx y hy hxy
  refine eq_of_periodicModel_eq D hN (hbd x hx) (hbd y hy) (fun g hg h0 ↦ ?_) hxy
  by_contra hne
  exact hnz _ (hTdiff x hx y hy g hg) (sub_ne_zero.mpr hne) h0

end CrossedProduct

end Pestov91
end GroupApproximation
