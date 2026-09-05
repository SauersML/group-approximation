import GroupApproximation.Analysis.FiniteCStarMurrayVonNeumann
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Bundle calculus VI: unit sections and the complementary bundle

A nowhere-vanishing section of a bundle splits a trivial line off it.  In the
projection model that statement is *unstable*: it does not say that `P` becomes
`P' ⊕ 1` in a bigger matrix algebra -- stabilising is exactly what destroys the
obstruction the LIX counterexample turns on -- it says that inside `M_ι(A)` the
projection `P` decomposes as

    P = perp P ξ + rankOneProj ξ,     perp P ξ * rankOneProj ξ = 0,

with `rankOneProj ξ` Murray-von Neumann equivalent to a single matrix unit, so a
genuinely trivial line.  `perp P ξ` is the object the Euler-class argument is
about, so it is a definition and not an existential.

Everything here is pure `*`-ring algebra over a commutative star ring, and it
rests on one computation: rank-one matrices multiply by contracting the inner
pair,

    (a b*) (c d*) = ⟨b, c⟩ (a d*),

which is `vecMulVec_mul_vecMulVec`.  Idempotence of `rankOneProj ξ`, absorption
`P · ξξ* = ξξ*`, and the equivalence with `Matrix.single i₀ i₀ 1` are all that
computation with different vectors substituted.

Nothing in this file mentions a topology, so nothing in it can be broken by the
analytic layer; the coefficient ring `R` is where the base space eventually
lives, as `R = C(X, ℂ)`, and there the unit-length condition
`∑ i, ξᵢ* ξᵢ = 1` says exactly `∀ x, ∑ i, ‖ξ i x‖ ^ 2 = 1`.

## Manuscript status

Machinery for the Euler-class interface (`found-euler-class`, manuscript
Lemma 2).  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace BundleCalculus

section RankOne

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] [StarRing R]

/-- The rank-one projection onto the line spanned by `ξ`, as the matrix `ξ ξ*`. -/
def rankOneProj (ξ : ι → R) : Matrix ι ι R := Matrix.vecMulVec ξ (star ξ)

@[simp]
theorem rankOneProj_apply (ξ : ι → R) (i j : ι) :
    rankOneProj ξ i j = ξ i * star (ξ j) := rfl

/-- **Rank-one matrices multiply by contracting the inner pair.**  Every other
computation in this file is this one with different vectors substituted. -/
theorem vecMulVec_mul_vecMulVec (a b c d : ι → R) :
    Matrix.vecMulVec a b * Matrix.vecMulVec c d
      = (∑ k, b k * c k) • Matrix.vecMulVec a d := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem star_vecMulVec (a b : ι → R) :
    star (Matrix.vecMulVec a b) = Matrix.vecMulVec (star b) (star a) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_vecMulVec]

theorem isSelfAdjoint_rankOneProj (ξ : ι → R) : IsSelfAdjoint (rankOneProj ξ) := by
  show star (rankOneProj ξ) = rankOneProj ξ
  show star (Matrix.vecMulVec ξ (star ξ)) = Matrix.vecMulVec ξ (star ξ)
  rw [star_vecMulVec, star_star]

/-- A **unit section** of the bundle `P`: a section of `P` of unit length.  Over
`R = C(X, ℂ)` the second field says exactly `∀ x, ∑ i, ‖ξ i x‖ ^ 2 = 1`, and the
first is `P *ᵥ ξ = ξ` in Mathlib's `mulVec` notation. -/
structure IsUnitSection (P : Matrix ι ι R) (ξ : ι → R) : Prop where
  mulVec_eq : Matrix.mulVec P ξ = ξ
  sum_star_mul_self : ∑ k, star (ξ k) * ξ k = 1

variable {P : Matrix ι ι R} {ξ : ι → R}

theorem isIdempotentElem_rankOneProj (hξ : IsUnitSection P ξ) :
    IsIdempotentElem (rankOneProj ξ) := by
  show Matrix.vecMulVec ξ (star ξ) * Matrix.vecMulVec ξ (star ξ)
      = Matrix.vecMulVec ξ (star ξ)
  rw [vecMulVec_mul_vecMulVec]
  simp only [Pi.star_apply]
  rw [hξ.sum_star_mul_self, one_smul]

theorem isStarProjection_rankOneProj (hξ : IsUnitSection P ξ) :
    IsStarProjection (rankOneProj ξ) where
  isIdempotentElem := isIdempotentElem_rankOneProj hξ
  isSelfAdjoint := isSelfAdjoint_rankOneProj ξ

/-- A bundle absorbs the line spanned by one of its sections. -/
theorem mul_rankOneProj (hξ : Matrix.mulVec P ξ = ξ) :
    P * rankOneProj ξ = rankOneProj ξ := by
  ext i j
  simp only [Matrix.mul_apply, rankOneProj_apply, ← mul_assoc, ← Finset.sum_mul]
  congr 1
  exact congrFun hξ i

theorem rankOneProj_mul (hP : IsStarProjection P) (hξ : Matrix.mulVec P ξ = ξ) :
    rankOneProj ξ * P = rankOneProj ξ := by
  have h := congrArg star (mul_rankOneProj (P := P) hξ)
  rw [star_mul, hP.isSelfAdjoint.star_eq, (isSelfAdjoint_rankOneProj ξ).star_eq] at h
  exact h

end RankOne

section Perp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] [StarRing R]
variable {P : Matrix ι ι R} {ξ : ι → R}

/-- The **complementary bundle** of a unit section: what is left of `P` after the
line spanned by `ξ` is removed.  A definition rather than an existential,
because it is the object the Euler-class argument is about. -/
def perp (P : Matrix ι ι R) (ξ : ι → R) : Matrix ι ι R := P - rankOneProj ξ

@[simp]
theorem perp_apply (P : Matrix ι ι R) (ξ : ι → R) (i j : ι) :
    perp P ξ i j = P i j - ξ i * star (ξ j) := rfl

/-- The decomposition, stated *inside* `M_ι(R)`: no stabilisation. -/
theorem perp_add_rankOneProj (P : Matrix ι ι R) (ξ : ι → R) :
    perp P ξ + rankOneProj ξ = P := by
  show P - rankOneProj ξ + rankOneProj ξ = P
  abel

theorem perp_mul_rankOneProj (hξ : IsUnitSection P ξ) :
    perp P ξ * rankOneProj ξ = 0 := by
  show (P - rankOneProj ξ) * rankOneProj ξ = 0
  rw [sub_mul, mul_rankOneProj hξ.mulVec_eq,
    (isIdempotentElem_rankOneProj hξ).eq, sub_self]

theorem rankOneProj_mul_perp (hP : IsStarProjection P) (hξ : IsUnitSection P ξ) :
    rankOneProj ξ * perp P ξ = 0 := by
  show rankOneProj ξ * (P - rankOneProj ξ) = 0
  rw [mul_sub, rankOneProj_mul hP hξ.mulVec_eq,
    (isIdempotentElem_rankOneProj hξ).eq, sub_self]

/-- The complement of a unit section inside a bundle is again a bundle. -/
theorem isStarProjection_perp (hP : IsStarProjection P) (hξ : IsUnitSection P ξ) :
    IsStarProjection (perp P ξ) where
  isIdempotentElem := by
    show (P - rankOneProj ξ) * (P - rankOneProj ξ) = P - rankOneProj ξ
    rw [sub_mul, mul_sub, mul_sub, hP.isIdempotentElem.eq,
      mul_rankOneProj hξ.mulVec_eq, rankOneProj_mul hP hξ.mulVec_eq,
      (isIdempotentElem_rankOneProj hξ).eq]
    abel
  isSelfAdjoint := hP.isSelfAdjoint.sub (isSelfAdjoint_rankOneProj ξ)

/-- **The line really is trivial.**  The rank-one projection on a unit section is
Murray-von Neumann equivalent to a single matrix unit -- size-honestly, without
leaving `M_ι(R)`.  The implementing partial isometry is `u ξ*` for `u` the
standard basis vector at `i₀`. -/
theorem murrayVonNeumannEquiv_rankOneProj_single (i₀ : ι) (hξ : IsUnitSection P ξ) :
    MurrayVonNeumannEquiv (rankOneProj ξ) (Matrix.single i₀ i₀ (1 : R)) := by
  classical
  set u : ι → R := fun k => if k = i₀ then (1 : R) else 0 with hu
  have hterm : ∀ k, star (u k) * u k = if k = i₀ then (1 : R) else 0 := by
    intro k
    by_cases h : k = i₀ <;> simp [hu, h]
  have hsum : ∑ k, star (u k) * u k = 1 := by simp [hterm]
  refine ⟨Matrix.vecMulVec u (star ξ), ?_, ?_⟩
  · show star (Matrix.vecMulVec u (star ξ)) * Matrix.vecMulVec u (star ξ)
        = Matrix.vecMulVec ξ (star ξ)
    rw [star_vecMulVec, star_star, vecMulVec_mul_vecMulVec]
    simp only [Pi.star_apply]
    rw [hsum, one_smul]
  · rw [star_vecMulVec, star_star, vecMulVec_mul_vecMulVec]
    simp only [Pi.star_apply]
    rw [hξ.sum_star_mul_self, one_smul]
    ext i j
    by_cases hi : i = i₀
    · subst hi
      by_cases hj : j = i₀
      · subst hj
        simp [hu, Matrix.vecMulVec_apply, Matrix.single_apply]
      · simp [hu, Matrix.vecMulVec_apply, Matrix.single_apply, hj, Ne.symm hj]
    · simp [hu, Matrix.vecMulVec_apply, Matrix.single_apply, hi, Ne.symm hi]

end Perp

end BundleCalculus
end GroupApproximation
