import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin dilation, analytic half, part 2: dilations of the variable and denominators

Lane `bh-met-76`.  For a commutative ring `B` and `u ∈ B`, `suslinDilAnDilate u` is the
substitution `f(Y) ↦ f(uY)` of `B[Y]`.  For a ring homomorphism `φ : B → S` and `s ∈ B`:

* if every `c ∈ S` has `c φ(s)^t ∈ φ(B)`, then every `f ∈ S[Y]` has `f φ(s)^t ∈ φ(B[Y])`
  (`suslinDilAn_surj_poly`);
* if `φ(b) = 0` forces `s^n b = 0`, the same holds on `B[Y]` (`suslinDilAn_ker_poly`);
* a polynomial `g` with `g(0) = 0` and `u g = 0` satisfies `g(uY) = 0`
  (`suslinDilAn_dilate_eq_zero`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

section Dilate

variable {B : Type*} [CommRing B]

/-- `f(Y) ↦ f(uY)`, as a ring endomorphism of `B[Y]`. -/
noncomputable def suslinDilAnDilate (u : B) : Polynomial B →+* Polynomial B :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.C u * Polynomial.X)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAnDilate

theorem suslinDilAnDilate_C (u b : B) : suslinDilAnDilate u (Polynomial.C b) = Polynomial.C b := by
  rw [suslinDilAnDilate, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAnDilate_C

theorem suslinDilAnDilate_X (u : B) :
    suslinDilAnDilate u Polynomial.X = Polynomial.C u * Polynomial.X := by
  rw [suslinDilAnDilate, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAnDilate_X

theorem suslinDilAnDilate_comp (u v : B) :
    (suslinDilAnDilate u).comp (suslinDilAnDilate v) = suslinDilAnDilate (u * v) := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, suslinDilAnDilate_C]
  · simp only [RingHom.comp_apply, suslinDilAnDilate_X, map_mul, suslinDilAnDilate_C]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAnDilate_comp

theorem suslinDilAnDilate_constantCoeff (u : B) :
    (Polynomial.constantCoeff (R := B)).comp (suslinDilAnDilate u) =
      Polynomial.constantCoeff (R := B) := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, suslinDilAnDilate_C]
  · simp only [RingHom.comp_apply, suslinDilAnDilate_X, Polynomial.constantCoeff_apply,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, mul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAnDilate_constantCoeff

theorem suslinDilAnDilate_comp_mapRingHom {S : Type*} [CommRing S] (φ : B →+* S) (u : B) :
    (suslinDilAnDilate (φ u)).comp (Polynomial.mapRingHom φ) =
      (Polynomial.mapRingHom φ).comp (suslinDilAnDilate u) := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
      suslinDilAnDilate_C]
  · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
      suslinDilAnDilate_X, Polynomial.map_mul, Polynomial.map_C]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAnDilate_comp_mapRingHom

/-- A polynomial vanishing at `0` and killed by `u` is killed by `Y ↦ uY`. -/
theorem suslinDilAn_dilate_eq_zero {u : B} {g : Polynomial B}
    (h0 : Polynomial.constantCoeff g = 0) (h : Polynomial.C u * g = 0) :
    suslinDilAnDilate u g = 0 := by
  rw [Polynomial.constantCoeff_apply] at h0
  obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.2 h0
  have hq : Polynomial.C u * q = 0 := by
    ext i
    have hi := congrArg (fun p ↦ Polynomial.coeff p (i + 1)) h
    simp only [Polynomial.coeff_zero] at hi ⊢
    rwa [mul_left_comm, Polynomial.coeff_X_mul] at hi
  rw [map_mul, suslinDilAnDilate_X, mul_comm (Polynomial.C u) Polynomial.X, mul_assoc,
    ← suslinDilAnDilate_C u u, ← map_mul, hq, map_zero, mul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_dilate_eq_zero

end Dilate

section Lift

variable {B S : Type*} [CommRing B] [CommRing S] (φ : B →+* S) (s : B)

/-- Denominators pass to polynomials: if every `c ∈ S` has `c φ(s)^t ∈ φ(B)`, then every
`f ∈ S[Y]` has `f φ(s)^t ∈ φ(B[Y])`. -/
theorem suslinDilAn_surj_poly (hsurj : ∀ c : S, ∃ (t : ℕ) (a : B), c * φ s ^ t = φ a)
    (f : Polynomial S) :
    ∃ (t : ℕ) (g : Polynomial B),
      f * Polynomial.mapRingHom φ (Polynomial.C s) ^ t = Polynomial.mapRingHom φ g := by
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_C]
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨t₁, g₁, h₁⟩ := hp
    obtain ⟨t₂, g₂, h₂⟩ := hq
    refine ⟨t₁ + t₂, g₁ * Polynomial.C s ^ t₂ + g₂ * Polynomial.C s ^ t₁, ?_⟩
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_pow, Polynomial.map_C, ← h₁, ← h₂]
    ring
  | monomial n c =>
    obtain ⟨t, a, h⟩ := hsurj c
    refine ⟨t, Polynomial.monomial n a, ?_⟩
    rw [← Polynomial.C_pow, Polynomial.monomial_mul_C, h, Polynomial.map_monomial]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_surj_poly

/-- Kernels pass to polynomials: if `φ(b) = 0` forces `s^n b = 0`, the same holds on `B[Y]`. -/
theorem suslinDilAn_ker_poly (hker : ∀ b : B, φ b = 0 → ∃ n : ℕ, s ^ n * b = 0)
    (g : Polynomial B) (hg : Polynomial.mapRingHom φ g = 0) :
    ∃ n : ℕ, Polynomial.C s ^ n * g = 0 := by
  rw [Polynomial.coe_mapRingHom] at hg
  have hc : ∀ i : ℕ, ∃ n : ℕ, s ^ n * g.coeff i = 0 := fun i ↦ hker _ (by
    rw [← Polynomial.coeff_map φ, hg, Polynomial.coeff_zero])
  choose n hn using hc
  refine ⟨g.support.sup n, ?_⟩
  ext i
  rw [← Polynomial.C_pow, Polynomial.coeff_C_mul, Polynomial.coeff_zero]
  by_cases hi : i ∈ g.support
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n) hi)
    rw [hd, pow_add, mul_comm (s ^ n i) (s ^ d), mul_assoc, hn i, mul_zero]
  · rw [Polynomial.notMem_support_iff.1 hi, mul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_ker_poly

theorem suslinDilAn_C_pow_mul_mono {u : B} {g : Polynomial B} {n m : ℕ}
    (h : Polynomial.C u ^ n * g = 0) (hnm : n ≤ m) : Polynomial.C u ^ m * g = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, mul_comm (Polynomial.C u ^ n), mul_assoc, h, mul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_C_pow_mul_mono

end Lift

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
