import GroupApproximation.Analysis.UniversalCoefficientTheorem
import GroupApproximation.Analysis.CStarOrderZero

/-!
# Dadarlat--Eilers stable uniqueness

Dadarlat and Eilers, *On the classification of nuclear C⋆-algebras*, Proc.
London Math. Soc. (3) **85** (2002), 168--210, Theorem 4.2 --- the **stable
uniqueness theorem**:

> if `φ, ψ : A → B` are `⋆`-homomorphisms from a separable nuclear C⋆-algebra
> satisfying the UCT which agree in `KK(A, B)`, then after adding a common
> summand they become approximately unitarily equivalent: for every finite set
> `F ⊆ A` and every `ε > 0` there are a `⋆`-homomorphism `σ : A → B` and a
> unitary `u` with `‖u (φ ⊕ σ)(a) u⋆ − (ψ ⊕ σ)(a)‖ < ε` for all `a ∈ F`.

This is the theorem through which the UCT enters Tikuisis--White--Winter: it
is what converts the `KK`-theoretic information supplied by the UCT into the
*approximate unitary equivalence* of two maps into a corona algebra, which is
what a quasidiagonality argument can use.

## What is proved here, and what is assumed

**Proved, unconditionally: the direct sum.**  Writing `φ ⊕ σ` requires a
target that can absorb two copies of itself.  In the multiplier-algebra
formulation this is `B ⊗ K`; here it is packaged as an `Amplifier` --- a pair
of isometries with orthogonal ranges summing to `1`, i.e. a unital copy of the
Cuntz algebra `O₂`'s generating relations --- and

* `Amplifier.oplus` is the map `a ↦ s₁ φ(a) s₁⋆ + s₂ ψ(a) s₂⋆`;
* `oplus_mul`, `oplus_one`, `oplus_star`, `oplus_add`, `oplus_smul`,
  `oplus_algebraMap` prove it is again a `⋆`-homomorphism when `φ` and `ψ`
  are, with genuine proofs from the four amplifier relations;
* `oplus_orthogonal` proves the same construction preserves orthogonality,
  which is what makes direct sums of *order-zero* maps order zero.

**Assumed: the theorem.**  `DadarlatEilersInput` states stable uniqueness over
a `KasparovTheory`.  It is a structure; no inhabitant is constructed here, and
none can be --- its proof is an induction over the bootstrap class, resting on
Kasparov's theory, the UCT, and absorption results for full
`⋆`-homomorphisms.

The input is stated in the *unital, single-algebra* form (`B` unital with an
amplifier, `u` a unitary of `B`) rather than with multiplier algebras and
`B ⊗ K`.  That is weaker than the published theorem, not stronger: an
application must supply the amplifier, and the corona algebra
`∏ Mₖ / ⊕ Mₖ` --- the only place this development applies it --- does supply
one.
-/

namespace GroupApproximation
namespace KK

open OrderZero

universe u v

noncomputable section

/-! ## Amplifiers and direct sums -/

/-- **An amplifier** of a unital C⋆-algebra: two isometries whose ranges are
orthogonal and exhaust the unit.  Equivalently, a unital `⋆`-homomorphism
from the Cuntz algebra `O₂`; equivalently, a `2 × 2` matrix unit system.  It
is what lets `B` absorb the direct sum of two maps into `B`.

A corona `∏ Mₖ / ⊕ Mₖ` carries one as soon as the matrix sizes grow, which is
the case the quasidiagonality argument meets. -/
structure Amplifier (B : Type v) [CStarAlgebra B] where
  /-- The first isometry. -/
  fst : B
  /-- The second isometry. -/
  snd : B
  /-- `fst` is an isometry. -/
  fst_isometry : star fst * fst = 1
  /-- `snd` is an isometry. -/
  snd_isometry : star snd * snd = 1
  /-- The ranges are orthogonal. -/
  orthogonal : star fst * snd = 0
  /-- The ranges exhaust the unit. -/
  range_sum : fst * star fst + snd * star snd = 1

namespace Amplifier

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
variable (E : Amplifier B)

/-- Orthogonality in the other order, by taking adjoints. -/
theorem orthogonal' : star E.snd * E.fst = 0 := by
  have h : star (star E.fst * E.snd) = star (0 : B) := by rw [E.orthogonal]
  rw [star_mul, star_star, star_zero] at h
  exact h

/-- **The direct sum of two maps** through an amplifier. -/
def oplus (φ ψ : A → B) : A → B :=
  fun a => E.fst * φ a * star E.fst + E.snd * ψ a * star E.snd

omit [CStarAlgebra A] in
@[simp] theorem oplus_apply (φ ψ : A → B) (a : A) :
    E.oplus φ ψ a = E.fst * φ a * star E.fst + E.snd * ψ a * star E.snd := rfl

/-! ### The four multiplication identities -/

theorem fst_mul_fst (x y : B) :
    (E.fst * x * star E.fst) * (E.fst * y * star E.fst)
      = E.fst * (x * y) * star E.fst := by
  calc (E.fst * x * star E.fst) * (E.fst * y * star E.fst)
      = E.fst * x * (star E.fst * E.fst) * y * star E.fst := by
        simp only [mul_assoc]
    _ = E.fst * x * 1 * y * star E.fst := by rw [E.fst_isometry]
    _ = E.fst * (x * y) * star E.fst := by
        rw [mul_one]; simp only [mul_assoc]

theorem snd_mul_snd (x y : B) :
    (E.snd * x * star E.snd) * (E.snd * y * star E.snd)
      = E.snd * (x * y) * star E.snd := by
  calc (E.snd * x * star E.snd) * (E.snd * y * star E.snd)
      = E.snd * x * (star E.snd * E.snd) * y * star E.snd := by
        simp only [mul_assoc]
    _ = E.snd * x * 1 * y * star E.snd := by rw [E.snd_isometry]
    _ = E.snd * (x * y) * star E.snd := by
        rw [mul_one]; simp only [mul_assoc]

theorem fst_mul_snd (x y : B) :
    (E.fst * x * star E.fst) * (E.snd * y * star E.snd) = 0 := by
  calc (E.fst * x * star E.fst) * (E.snd * y * star E.snd)
      = E.fst * x * (star E.fst * E.snd) * y * star E.snd := by
        simp only [mul_assoc]
    _ = E.fst * x * 0 * y * star E.snd := by rw [E.orthogonal]
    _ = 0 := by rw [mul_zero, zero_mul, zero_mul]

theorem snd_mul_fst (x y : B) :
    (E.snd * x * star E.snd) * (E.fst * y * star E.fst) = 0 := by
  calc (E.snd * x * star E.snd) * (E.fst * y * star E.fst)
      = E.snd * x * (star E.snd * E.fst) * y * star E.fst := by
        simp only [mul_assoc]
    _ = E.snd * x * 0 * y * star E.fst := by rw [E.orthogonal']
    _ = 0 := by rw [mul_zero, zero_mul, zero_mul]

/-! ### The direct sum of `⋆`-homomorphisms -/

/-- **Multiplicativity of the direct sum**: the cross terms vanish because the
ranges of the two isometries are orthogonal, and the diagonal terms collapse
because they are isometries. -/
theorem oplus_mul (φ ψ : A → B)
    (hφ : ∀ x y : A, φ (x * y) = φ x * φ y)
    (hψ : ∀ x y : A, ψ (x * y) = ψ x * ψ y) (a b : A) :
    E.oplus φ ψ (a * b) = E.oplus φ ψ a * E.oplus φ ψ b := by
  rw [oplus_apply, oplus_apply, oplus_apply, hφ a b, hψ a b, add_mul,
    mul_add, mul_add, E.fst_mul_fst, E.fst_mul_snd, E.snd_mul_fst,
    E.snd_mul_snd, add_zero, zero_add]

/-- The direct sum of two unital maps is unital. -/
theorem oplus_one (φ ψ : A → B) (hφ : φ 1 = 1) (hψ : ψ 1 = 1) :
    E.oplus φ ψ 1 = 1 := by
  rw [oplus_apply, hφ, hψ, mul_one, mul_one, E.range_sum]

/-- Adjoints pass through a conjugation `x ↦ s x s⋆`. -/
theorem star_conj (s x : B) : star (s * x * star s) = s * star x * star s := by
  rw [star_mul, star_mul, star_star, mul_assoc]

/-- The direct sum of two `⋆`-preserving maps is `⋆`-preserving. -/
theorem oplus_star (φ ψ : A → B)
    (hφ : ∀ x : A, φ (star x) = star (φ x))
    (hψ : ∀ x : A, ψ (star x) = star (ψ x)) (a : A) :
    E.oplus φ ψ (star a) = star (E.oplus φ ψ a) := by
  rw [oplus_apply, oplus_apply, hφ, hψ, star_add, star_conj, star_conj]

/-- The direct sum of two additive maps is additive. -/
theorem oplus_add (φ ψ : A → B)
    (hφ : ∀ x y : A, φ (x + y) = φ x + φ y)
    (hψ : ∀ x y : A, ψ (x + y) = ψ x + ψ y) (a b : A) :
    E.oplus φ ψ (a + b) = E.oplus φ ψ a + E.oplus φ ψ b := by
  rw [oplus_apply, oplus_apply, oplus_apply, hφ, hψ, mul_add, mul_add,
    add_mul, add_mul]
  abel

/-- The direct sum of two `ℂ`-linear maps is `ℂ`-linear. -/
theorem oplus_smul (φ ψ : A → B)
    (hφ : ∀ (c : ℂ) (x : A), φ (c • x) = c • φ x)
    (hψ : ∀ (c : ℂ) (x : A), ψ (c • x) = c • ψ x) (c : ℂ) (a : A) :
    E.oplus φ ψ (c • a) = c • E.oplus φ ψ a := by
  rw [oplus_apply, oplus_apply, hφ, hψ, mul_smul_comm, smul_mul_assoc,
    mul_smul_comm, smul_mul_assoc, smul_add]

/-- The direct sum of two algebra maps is an algebra map: the scalars are
central, so they pull out of both conjugations and meet the amplifier
relation. -/
theorem oplus_algebraMap (φ ψ : A → B)
    (hφ : ∀ c : ℂ, φ (algebraMap ℂ A c) = algebraMap ℂ B c)
    (hψ : ∀ c : ℂ, ψ (algebraMap ℂ A c) = algebraMap ℂ B c) (c : ℂ) :
    E.oplus φ ψ (algebraMap ℂ A c) = algebraMap ℂ B c := by
  rw [oplus_apply, hφ, hψ, ← Algebra.commutes c E.fst,
    ← Algebra.commutes c E.snd, mul_assoc, mul_assoc, ← mul_add,
    E.range_sum, mul_one]

omit [CStarAlgebra A] in
/-- **The direct sum preserves orthogonality.**  This is the clause that makes
a direct sum of order-zero maps order zero: the same computation as
`oplus_mul`, with the diagonal terms vanishing instead of collapsing. -/
theorem oplus_orthogonal (φ ψ : A → B) {a b : A}
    (hφ : φ a * φ b = 0) (hψ : ψ a * ψ b = 0) :
    E.oplus φ ψ a * E.oplus φ ψ b = 0 := by
  rw [oplus_apply, oplus_apply, add_mul, mul_add, mul_add, E.fst_mul_fst,
    E.fst_mul_snd, E.snd_mul_fst, E.snd_mul_snd, hφ, hψ, mul_zero, zero_mul,
    mul_zero, zero_mul, add_zero, add_zero]

omit [CStarAlgebra A] in
/-- The direct sum is a contraction as soon as both summands are, since the
two terms have orthogonal ranges.  Stated as the crude triangle-inequality
bound, which is all any application here needs. -/
theorem norm_oplus_le (φ ψ : A → B) (a : A) :
    ‖E.oplus φ ψ a‖
      ≤ ‖E.fst‖ * ‖φ a‖ * ‖star E.fst‖ + ‖E.snd‖ * ‖ψ a‖ * ‖star E.snd‖ := by
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · exact le_trans (norm_mul_le _ _)
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  · exact le_trans (norm_mul_le _ _)
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

end Amplifier

/-! ## The stable uniqueness theorem, as a typed input -/

/-- **Dadarlat--Eilers stable uniqueness, as a typed input.**

Two `⋆`-homomorphisms out of a separable nuclear UCT algebra that agree in
`KK` become approximately unitarily equivalent after adding a common summand.

`nuclear` is the completely positive approximation property
(`CStarExactness.IsNuclearCStarAlgebra`), which is the form
`Analysis.TikuisisWhiteWinter` fixed for the whole chain; `SatisfiesUCT` is
the *defined* bootstrap-class predicate of
`Analysis.UniversalCoefficientTheorem`, no longer a free parameter.

**No inhabitant is constructed here.**  The conclusion is deliberately weaker
than the published one in two respects: the summand `σ` is not asserted to be
full or repeatable, and the unitary is taken in `B` rather than in a
multiplier algebra.  Both weakenings make the input easier to satisfy and the
theorems below correspondingly stronger. -/
structure DadarlatEilersInput (T : KasparovTheory.{u}) : Prop where
  /-- Stable uniqueness. -/
  stable_uniqueness :
    ∀ (A B : SepCStarAlgebra.{u}),
      CStarExactness.IsNuclearCStarAlgebra A →
        T.SatisfiesUCT A →
          ∀ (E : Amplifier B) (φ ψ : A →⋆ₐ[ℂ] B),
            T.classOf φ = T.classOf ψ →
              ∀ (F : Finset A) (ε : ℝ), 0 < ε →
                ∃ (σ : A →⋆ₐ[ℂ] B) (u : B), star u * u = 1 ∧ u * star u = 1 ∧
                  ∀ a ∈ F,
                    ‖u * E.oplus (fun x => φ x) (fun x => σ x) a * star u
                      - E.oplus (fun x => ψ x) (fun x => σ x) a‖ < ε

/-- **The shape the quasidiagonality argument uses.**  With the summand and
the unitary existentially quantified, stable uniqueness says exactly that two
`KK`-equal maps are *approximately unitarily equivalent after amplification*.

Proved from the input, and recorded separately because it is the form
`Analysis.TikuisisWhiteWinterProof` cites: it removes the `Finset`/`ε`
bookkeeping from the citation site. -/
theorem approx_unitary_equiv_of_kk_eq {T : KasparovTheory.{u}}
    (de : DadarlatEilersInput T) {A B : SepCStarAlgebra.{u}}
    (hnuc : CStarExactness.IsNuclearCStarAlgebra A) (huct : T.SatisfiesUCT A)
    (E : Amplifier B) (φ ψ : A →⋆ₐ[ℂ] B) (hkk : T.classOf φ = T.classOf ψ)
    (F : Finset A) {ε : ℝ} (hε : 0 < ε) :
    ∃ (σ : A →⋆ₐ[ℂ] B) (u : B), star u * u = 1 ∧ u * star u = 1 ∧
      ∀ a ∈ F,
        ‖u * E.oplus (fun x => φ x) (fun x => σ x) a * star u
          - E.oplus (fun x => ψ x) (fun x => σ x) a‖ < ε :=
  de.stable_uniqueness A B hnuc huct E φ ψ hkk F ε hε

end

end KK
end GroupApproximation
