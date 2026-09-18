import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Matrix.ToLin
import GroupApproximation.BooneHigman.Coordinates.MatrixEmbedding
import GroupApproximation.Meta.AxiomGuard

/-!
# Left multiplication on a localized algebra (lane bh-met-10)

Research node `char-p-polynomial-embedding-via-noether-normalization`, step "generic freeness
... then `A_f` is free over `P_f`, so `A_f` embeds in a matrix ring over `P_f`", together with
"`A ⊆ A_f`".

For a `P`-algebra `A` and `r ∈ P`, left multiplication by `x ∈ A` localizes to a
`P[1/r]`-linear endomorphism of `A[1/r] = LocalizedModule (powers r) A`
(`awayMulLeft`).  If `A` is a domain and no power of `r` maps to `0` in `A`, this ring
homomorphism `A → End_{P[1/r]}(A[1/r])` is injective (`awayMulLeft_injective`), because it
sends `x` to an endomorphism mapping `1/1` to `x/1`.  A finite `P[1/r]`-basis of `A[1/r]` then
turns the endomorphisms into matrices (`matrixEmbedding_of_basis_away`).

The ring structure of `LocalizedModule` is never used: the endomorphisms are obtained from
`IsLocalizedModule.map` applied to `LinearMap.mul P A x`.
-/

open GroupApproximation.BooneHigman.Coordinates

namespace GroupApproximation.BooneHigman.Metabelian.CharPCoords

variable {P A : Type*} [CommRing P] [CommRing A] [Algebra P A]

/-- Left multiplication by `x ∈ A`, localized at the powers of `r ∈ P`, as a
`P[1/r]`-linear endomorphism of `A[1/r]`. -/
noncomputable def awayMulLeft (r : P) :
    A →+* Module.End (Localization.Away r) (LocalizedModule.Away r A) where
  toFun x := (IsLocalizedModule.map (Submonoid.powers r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) A)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) A)
      (LinearMap.mul P A x)).extendScalarsOfIsLocalization (Submonoid.powers r)
      (Localization.Away r)
  map_one' := by
    refine LinearMap.ext fun m => ?_
    induction m using LocalizedModule.induction_on with
    | h a u =>
      simp only [LinearMap.extendScalarsOfIsLocalization_apply',
        IsLocalizedModule.map_LocalizedModules, LinearMap.mul_apply', one_mul,
        Module.End.one_apply]
  map_mul' x y := by
    refine LinearMap.ext fun m => ?_
    induction m using LocalizedModule.induction_on with
    | h a u =>
      simp only [LinearMap.extendScalarsOfIsLocalization_apply',
        IsLocalizedModule.map_LocalizedModules, LinearMap.mul_apply', mul_assoc,
        Module.End.mul_apply]
  map_zero' := by
    refine LinearMap.ext fun m => ?_
    simp only [LinearMap.extendScalarsOfIsLocalization_apply', map_zero, LinearMap.zero_apply]
  map_add' x y := by
    refine LinearMap.ext fun m => ?_
    simp only [LinearMap.extendScalarsOfIsLocalization_apply', map_add, LinearMap.add_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.awayMulLeft

/-- `awayMulLeft r x` sends `a/u` to `(x a)/u`. -/
theorem awayMulLeft_mk (r : P) (x a : A) (u : Submonoid.powers r) :
    awayMulLeft r x (LocalizedModule.mk a u) = LocalizedModule.mk (x * a) u := by
  change IsLocalizedModule.map (Submonoid.powers r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) A)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) A)
      (LinearMap.mul P A x) (LocalizedModule.mk a u) = _
  rw [IsLocalizedModule.map_LocalizedModules, LinearMap.mul_apply']

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.awayMulLeft_mk

/-- If `A` is a domain and no power of `r` maps to `0` in `A`, left multiplication on `A[1/r]`
is a faithful representation of `A`. -/
theorem awayMulLeft_injective [IsDomain A] {r : P}
    (hr : ∀ n : ℕ, algebraMap P A (r ^ n) ≠ 0) :
    Function.Injective (awayMulLeft (A := A) r) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  have h1 := LinearMap.congr_fun hx (LocalizedModule.mk (1 : A) (1 : Submonoid.powers r))
  rw [awayMulLeft_mk, mul_one, LinearMap.zero_apply] at h1
  have h2 : LocalizedModule.mk x (1 : Submonoid.powers r) =
      LocalizedModule.mk (0 : A) (1 : Submonoid.powers r) := by
    rw [LocalizedModule.zero_mk]
    exact h1
  obtain ⟨⟨u, hu⟩, h3⟩ := LocalizedModule.mk_eq.mp h2
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hu
  simp only [one_smul, smul_zero, Submonoid.mk_smul] at h3
  rw [Algebra.smul_def] at h3
  exact (mul_eq_zero.mp h3).resolve_left (hr n)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.awayMulLeft_injective

/-- **Free localization gives a matrix embedding.**  Let `A` be a domain and a `P`-algebra with
`P → A` injective, `P` a domain, and `r ≠ 0`.  If `A[1/r]` has a finite basis over `P[1/r]`,
then `A` embeds in a matrix ring over `P[1/r]`. -/
theorem matrixEmbedding_of_basis_away [IsDomain P] [IsDomain A]
    (hinj : Function.Injective (algebraMap P A)) {r : P} (hr : r ≠ 0) {I : Type*} [Finite I]
    (b : Module.Basis I (Localization.Away r) (LocalizedModule.Away r A)) :
    MatrixEmbedding A (Localization.Away r) := by
  classical
  haveI : Fintype I := Fintype.ofFinite I
  have hpow : ∀ n : ℕ, algebraMap P A (r ^ n) ≠ 0 := fun n h =>
    pow_ne_zero n hr ((map_eq_zero_iff _ hinj).mp h)
  exact ⟨Fintype.card I,
    ((Matrix.reindexRingEquiv (R := Localization.Away r) (Fintype.equivFin I)).toRingHom.comp
      (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom).comp (awayMulLeft r),
    ((Matrix.reindexRingEquiv (R := Localization.Away r) (Fintype.equivFin I)).injective.comp
      (LinearMap.toMatrixAlgEquiv b).injective).comp (awayMulLeft_injective hpow)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharPCoords.matrixEmbedding_of_basis_away

end GroupApproximation.BooneHigman.Metabelian.CharPCoords
