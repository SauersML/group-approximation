import Mathlib.Algebra.Polynomial.Div
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
  · simp only [RingHom.comp_apply, suslinDilAnDilate_X, map_mul, Polynomial.constantCoeff_apply,
      Polynomial.coeff_X_zero, mul_zero]

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
