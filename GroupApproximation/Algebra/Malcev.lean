import GroupApproximation.Algebra.FiniteTypeField
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.ResiduallyFinite

/-!
# Sections 46.1 and 46.2: finite residue fields, and Mal'cev's theorem

**Lemma 46.1.**  In a finitely generated integral domain every nonzero element
survives in some finite field: invert it, take a maximal ideal of the
localization, and use that a field finitely generated as a ring is finite.

**Theorem 46.2.**  Consequently the general linear group over a finitely
generated domain is residually finite: a nonidentity matrix differs from the
identity in some entry, and a finite residue field for that entry gives a
finite quotient detecting it.  A finitely generated linear group over any field
lies in such a general linear group, which is the dossier's formulation.
-/

namespace GroupApproximation

universe u

/-- **Lemma 46.1.**  A nonzero element of a finitely generated domain is
detected by a homomorphism to a finite field. -/
theorem exists_finite_field_hom_of_ne_zero (R : Type u) [CommRing R] [IsDomain R]
    [Algebra.FiniteType ℤ R] {r : R} (hr : r ≠ 0) :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (f : R →+* k), f r ≠ 0 := by
  classical
  have hM : Submonoid.powers r ≤ nonZeroDivisors R := by
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact pow_mem (mem_nonZeroDivisors_of_ne_zero hr) n
  haveI : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away r) hM
  haveI : Algebra.FinitePresentation R (Localization.Away r) :=
    IsLocalization.Away.finitePresentation r
  haveI : Algebra.FiniteType R (Localization.Away r) := inferInstance
  haveI : Algebra.FiniteType ℤ (Localization.Away r) := by
    have h1 : Algebra.FiniteType ℤ R := inferInstance
    have h2 : Algebra.FiniteType R (Localization.Away r) := inferInstance
    exact Algebra.FiniteType.trans h1 h2
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (Localization.Away r)
  haveI := hm
  letI : Field (Localization.Away r ⧸ m) := Ideal.Quotient.field m
  -- a polynomial surjection onto the residue field
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType ℤ (Localization.Away r))
  haveI : Finite (Localization.Away r ⧸ m) := by
    refine finite_of_polynomial_surjective (Localization.Away r ⧸ m)
      ((Ideal.Quotient.mk m).comp g.toRingHom) ?_
    show Function.Surjective (fun x => (Ideal.Quotient.mk m) (g x))
    exact Function.Surjective.comp Ideal.Quotient.mk_surjective hg
  refine ⟨Localization.Away r ⧸ m, inferInstance, inferInstance,
    (Ideal.Quotient.mk m).comp (algebraMap R (Localization.Away r)), ?_⟩
  intro hzero
  have hunit : IsUnit ((Ideal.Quotient.mk m)
      (algebraMap R (Localization.Away r) r)) :=
    (IsLocalization.map_units (Localization.Away r)
      (⟨r, Submonoid.mem_powers r⟩ : Submonoid.powers r)).map _
  rw [RingHom.comp_apply] at hzero
  rw [hzero] at hunit
  exact not_isUnit_zero hunit

/-- **Theorem 46.2 (Mal'cev), matrix form.**  The general linear group over a
finitely generated domain is residually finite. -/
theorem residuallyFinite_generalLinearGroup (R : Type u) [CommRing R] [IsDomain R]
    [Algebra.FiniteType ℤ R] (d : ℕ) :
    Group.ResiduallyFinite (Matrix.GeneralLinearGroup (Fin d) R) := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro g hg
  -- some entry of `g - 1` is nonzero
  have hne : (g : Matrix (Fin d) (Fin d) R) ≠ 1 := by
    intro hcon
    exact hg (Units.ext hcon)
  obtain ⟨i, j, hij⟩ : ∃ i j, (g : Matrix (Fin d) (Fin d) R) i j
      ≠ (1 : Matrix (Fin d) (Fin d) R) i j := by
    by_contra hcon
    push Not at hcon
    exact hne (by
      ext i j
      exact hcon i j)
  have hsub : (g : Matrix (Fin d) (Fin d) R) i j
      - (1 : Matrix (Fin d) (Fin d) R) i j ≠ 0 := sub_ne_zero.mpr hij
  obtain ⟨k, hkfield, hkfin, f, hf⟩ := exists_finite_field_hom_of_ne_zero R hsub
  letI := hkfield
  haveI := hkfin
  refine ⟨Matrix.GeneralLinearGroup (Fin d) k, inferInstance, inferInstance,
    Units.map (f.mapMatrix : Matrix (Fin d) (Fin d) R →+* _).toMonoidHom, ?_⟩
  intro hcon
  apply hf
  have hentry : f ((g : Matrix (Fin d) (Fin d) R) i j)
      = (1 : Matrix (Fin d) (Fin d) k) i j := by
    have := congrArg (fun u : Matrix.GeneralLinearGroup (Fin d) k =>
      (u : Matrix (Fin d) (Fin d) k) i j) hcon
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using this
  rw [map_sub, hentry]
  have hone : f ((1 : Matrix (Fin d) (Fin d) R) i j)
      = (1 : Matrix (Fin d) (Fin d) k) i j := by
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hij' : i = j
    · rw [if_pos hij', if_pos hij', map_one]
    · rw [if_neg hij', if_neg hij', map_zero]
  rw [hone, sub_self]

end GroupApproximation
