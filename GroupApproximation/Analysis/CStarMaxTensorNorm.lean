import GroupApproximation.Analysis.CStarMinTensorNorm
import GroupApproximation.Analysis.CStarCompletionHom
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Star.TensorProduct

/-!
# The maximal tensor norm, and `A ⊗_max B` as a C⋆-algebra

## What this module builds

`CStarMinTensorNorm` builds the canonical *minimal* norm as a supremum over a
family of representations manufactured from states.  This module builds the
*maximal* one, which is the supremum over a family that cannot be manufactured
at all: **every** C⋆-seminorm on `A ⊙ B` under which the two factors act by
contractions.

* `IsTensorCStarSeminorm` is that family — a C⋆-seminorm `p` with
  `p (a ⊗ₜ 1) ≤ ‖a‖` and `p (1 ⊗ₜ b) ≤ ‖b‖`, which is what "contractive on
  both factors" says at the level of seminorms;
* `maxTensorNorm` is its pointwise supremum, a C⋆-seminorm by the supremum
  recipe, a **norm** because it dominates `minTensorNorm`, and a **cross norm
  on the nose** (`maxTensorNorm_tmul`);
* `MaxTensorProduct A B` is the completion, a C⋆-algebra through the
  `WithCStarNorm` chain, with `maxTensorIn` embedding the algebraic tensor
  product isometrically and densely;
* `maxTensorProduct_existsUnique_lift` is the universal property: a pair of
  ⋆-homomorphisms out of the two factors with commuting ranges factors
  uniquely through `A ⊗_max B`.

## Why the family is a set, and why that is the whole trick

"Supremum over all representations of `A ⊙ B` contractive on both factors" is a
supremum over a proper class.  The minimal norm escapes this by manufacturing a
*set* of representations out of states; nothing manufactures the representations
the maximal norm needs.  What is used instead is that a representation is only
ever consulted through the seminorm it induces, and a seminorm on `A ⊙ B` is a
function `(A ⊗[ℂ] B) → ℝ` — a set-sized object no matter where the
representation lives.  Indexing by seminorms rather than by representations is
the same device that gives the maximal group C⋆-algebra of
`Analysis/MaximalCStarPrintedCompletion` its universal property at every
universe, and it has the same consequence here: the target `C` of the universal
property below is quantified at a universe independent of `A` and `B`.

Two things then come for free, and both are worth naming because in the
textbook development they take work:

* **Definiteness.** `minTensorNorm` is itself a member of the family, so
  `minTensorNorm ≤ maxTensorNorm` is one application of `le_ciSup`, and
  `maxTensorNorm x = 0` forces `minTensorNorm x = 0`, which forces `x = 0`
  because the minimal norm is already known to be a norm.  No separate
  faithfulness argument for the maximal norm is needed.
* **Nonemptiness** of the index, needed before a supremum means anything, is
  witnessed by that same member.

## What is not claimed

**Nuclearity is now statable and is not claimed.**  `A` is nuclear when
`minTensorNorm = maxTensorNorm` for every `B`; with both norms defined, that
sentence is a well-formed proposition of this development for the first time.
Nothing here proves it in any instance, and nothing here proves its negation in
any instance either.  In particular this module does not show the two norms are
ever *different*, which is what a genuine `⊗_min ≠ ⊗_max` example would need.

Also not proved, and separate: that `maxTensorNorm` is the largest C⋆-norm on
`A ⊙ B` in the sense that dominates *any* C⋆-norm rather than any member of the
declared family; that requires knowing every C⋆-norm on `A ⊙ B` restricts to
contractions on the factors, which is a theorem about C⋆-norms
(`‖a ⊗ₜ 1‖ ≤ ‖a‖` for an arbitrary C⋆-norm) and is not established here.  The
family is therefore stated explicitly rather than as "all C⋆-norms", so that
what the supremum ranges over is visible in the definition.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `SO.16` and `RE.05`
remain **MISSING**: exactness needs the noncommutative C⋆-quotient, and
nuclearity needs a theorem relating the two norms, not merely both of them.
-/

namespace GroupApproximation
namespace CStarTensor

open scoped TensorProduct CStarAlgebra

universe u v w

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]

/-! ## The family the supremum is taken over -/

/-- A C⋆-seminorm on the algebraic tensor product under which **both factors
act by contractions**.

This is the seminorm-level reading of "a ⋆-representation of `A ⊙ B` that is
contractive on each factor": such a representation induces a C⋆-seminorm with
exactly these two bounds, and conversely only these two bounds are ever used. -/
structure IsTensorCStarSeminorm (p : (A ⊗[ℂ] B) → ℝ) : Prop where
  /-- It is a C⋆-seminorm. -/
  isCStarSeminorm : IsCStarSeminorm p
  /-- The left factor acts by contractions. -/
  left_le : ∀ a : A, p (a ⊗ₜ[ℂ] (1 : B)) ≤ ‖a‖
  /-- The right factor acts by contractions. -/
  right_le : ∀ b : B, p ((1 : A) ⊗ₜ[ℂ] b) ≤ ‖b‖

-- nontriviality of the factors is what makes `‖1‖ = 1`, which the members of
-- the family below need; the two bounds themselves do not use it
omit [Nontrivial A] [Nontrivial B] in
/-- Contractivity on each factor bounds an elementary tensor by the product of
the norms, because `a ⊗ₜ b` is the product of `a ⊗ₜ 1` and `1 ⊗ₜ b` and the
seminorm is submultiplicative. -/
theorem IsTensorCStarSeminorm.tmul_le {p : (A ⊗[ℂ] B) → ℝ}
    (hp : IsTensorCStarSeminorm p) (a : A) (b : B) :
    p (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖b‖ := by
  have hsplit : a ⊗ₜ[ℂ] b = (a ⊗ₜ[ℂ] (1 : B)) * ((1 : A) ⊗ₜ[ℂ] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hsplit]
  refine (hp.isCStarSeminorm.mul_le _ _).trans ?_
  exact mul_le_mul (hp.left_le a) (hp.right_le b)
    (hp.isCStarSeminorm.nonneg _) (norm_nonneg a)

omit [Nontrivial A] [Nontrivial B] in
/-- **The family is pointwise bounded.**  On an elementary tensor by
`‖a‖ * ‖b‖`, and in general by a sum of such bounds along any decomposition;
the bound is not the `ℓ¹` norm of a chosen decomposition but merely *some*
constant, which is all a supremum needs. -/
theorem exists_bound_of_isTensorCStarSeminorm (x : A ⊗[ℂ] B) :
    ∃ C : ℝ, ∀ p : (A ⊗[ℂ] B) → ℝ, IsTensorCStarSeminorm p → p x ≤ C := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun _ hp ↦ le_of_eq hp.isCStarSeminorm.map_zero⟩
  | tmul a b => exact ⟨‖a‖ * ‖b‖, fun _ hp ↦ hp.tmul_le a b⟩
  | add y z hy hz =>
      obtain ⟨Cy, hCy⟩ := hy
      obtain ⟨Cz, hCz⟩ := hz
      exact ⟨Cy + Cz, fun p hp ↦ (hp.isCStarSeminorm.add_le y z).trans
        (add_le_add (hCy p hp) (hCz p hp))⟩

omit [Nontrivial A] [Nontrivial B] in
theorem bddAbove_isTensorCStarSeminorm (x : A ⊗[ℂ] B) :
    BddAbove (Set.range fun q : {p : (A ⊗[ℂ] B) → ℝ // IsTensorCStarSeminorm p} ↦
      q.1 x) := by
  obtain ⟨C, hC⟩ := exists_bound_of_isTensorCStarSeminorm x
  refine ⟨C, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact hC q.1 q.2

/-- **The minimal norm is a member of the family.**  Its cross-norm identity
gives both bounds on the nose, since `‖1‖ = 1` in a nontrivial C⋆-algebra.
This is what makes the index nonempty and, below, what makes the maximal
seminorm definite. -/
theorem isTensorCStarSeminorm_minTensorNorm :
    IsTensorCStarSeminorm (minTensorNorm (A := A) (B := B)) where
  isCStarSeminorm := isCStarSeminorm_minTensorNorm
  left_le a := le_of_eq (by rw [minTensorNorm_tmul, CStarRing.norm_one, mul_one])
  right_le b := le_of_eq (by rw [minTensorNorm_tmul, CStarRing.norm_one, one_mul])

theorem nonempty_tensorCStarSeminorm :
    Nonempty {p : (A ⊗[ℂ] B) → ℝ // IsTensorCStarSeminorm p} :=
  ⟨⟨minTensorNorm, isTensorCStarSeminorm_minTensorNorm⟩⟩

/-! ## The maximal tensor norm -/

/-- **The maximal tensor norm**: the supremum of every C⋆-seminorm on the
algebraic tensor product under which both factors act by contractions. -/
noncomputable def maxTensorNorm : (A ⊗[ℂ] B) → ℝ :=
  iSupSeminorm fun q : {p : (A ⊗[ℂ] B) → ℝ // IsTensorCStarSeminorm p} ↦ q.1

omit [Nontrivial A] [Nontrivial B] in
/-- Every member of the family is dominated by the supremum. -/
theorem le_maxTensorNorm {p : (A ⊗[ℂ] B) → ℝ} (hp : IsTensorCStarSeminorm p)
    (x : A ⊗[ℂ] B) : p x ≤ maxTensorNorm x := by
  show p x ≤ ⨆ q : {r : (A ⊗[ℂ] B) → ℝ // IsTensorCStarSeminorm r}, q.1 x
  exact le_ciSup (bddAbove_isTensorCStarSeminorm x) ⟨p, hp⟩

theorem isCStarSeminorm_maxTensorNorm :
    IsCStarSeminorm (maxTensorNorm (A := A) (B := B)) :=
  isCStarSeminorm_iSup nonempty_tensorCStarSeminorm
    (fun q ↦ q.2.isCStarSeminorm) bddAbove_isTensorCStarSeminorm

/-- **The minimal norm is dominated by the maximal one.**  One application of
`le_ciSup`, because the minimal norm is a member of the family the maximal one
is the supremum of. -/
theorem minTensorNorm_le_maxTensorNorm (x : A ⊗[ℂ] B) :
    minTensorNorm x ≤ maxTensorNorm x :=
  le_maxTensorNorm isTensorCStarSeminorm_minTensorNorm x

/-- **The maximal tensor norm is a C⋆-norm.**  Definiteness is inherited from
the minimal norm through the domination above, so no faithfulness argument is
repeated for the maximal norm. -/
theorem isCStarNorm_maxTensorNorm :
    IsCStarNorm (maxTensorNorm (A := A) (B := B)) where
  isCStarSeminorm := isCStarSeminorm_maxTensorNorm
  eq_zero x hx := by
    refine isCStarNorm_minTensorNorm.eq_zero x
      (le_antisymm ?_ (isCStarSeminorm_minTensorNorm.nonneg x))
    rw [← hx]
    exact minTensorNorm_le_maxTensorNorm x

/-- **The maximal tensor norm is a cross norm on the nose.**  The upper bound
is the defining contractivity of the family; the lower bound is the minimal
norm's cross-norm identity, since the minimal norm is dominated by this one. -/
theorem maxTensorNorm_tmul (a : A) (b : B) :
    maxTensorNorm (a ⊗ₜ[ℂ] b) = ‖a‖ * ‖b‖ := by
  haveI := nonempty_tensorCStarSeminorm (A := A) (B := B)
  refine le_antisymm ?_ ?_
  · show (⨆ q : {r : (A ⊗[ℂ] B) → ℝ // IsTensorCStarSeminorm r},
      q.1 (a ⊗ₜ[ℂ] b)) ≤ ‖a‖ * ‖b‖
    exact ciSup_le fun q ↦ q.2.tmul_le a b
  · rw [← minTensorNorm_tmul a b]
    exact minTensorNorm_le_maxTensorNorm _

/-- The supremum is itself a member of the family: it is the largest one. -/
theorem isTensorCStarSeminorm_maxTensorNorm :
    IsTensorCStarSeminorm (maxTensorNorm (A := A) (B := B)) where
  isCStarSeminorm := isCStarSeminorm_maxTensorNorm
  left_le a := le_of_eq (by rw [maxTensorNorm_tmul, CStarRing.norm_one, mul_one])
  right_le b := le_of_eq (by rw [maxTensorNorm_tmul, CStarRing.norm_one, one_mul])

/-! ## The object: `A ⊗_max B` -/

variable (A B) in
/-- The algebraic tensor product retagged with the maximal C⋆-norm. -/
abbrev MaxPreTensor : Type (max u v) :=
  WithCStarNorm (isCStarNorm_maxTensorNorm (A := A) (B := B))

variable (A B) in
/-- **The maximal tensor product `A ⊗_max B`**: the completion of the algebraic
tensor product in the maximal C⋆-norm. -/
def MaxTensorProduct : Type (max u v) :=
  UniformSpace.Completion (MaxPreTensor A B)

noncomputable instance instCStarAlgebraMaxTensorProduct :
    CStarAlgebra (MaxTensorProduct A B) :=
  completionCStarAlgebraOfIsCStarNorm isCStarNorm_maxTensorNorm

variable (A B) in
/-- The canonical ⋆-algebra homomorphism from the algebraic tensor product into
`A ⊗_max B`. -/
noncomputable def maxTensorIn :
    (A ⊗[ℂ] B) →⋆ₐ[ℂ] MaxTensorProduct A B :=
  (CStarCompletion.coeStarAlgHom (MaxPreTensor A B)).comp
    (WithCStarNorm.retagStarAlgHom isCStarNorm_maxTensorNorm)

theorem norm_maxTensorIn (x : A ⊗[ℂ] B) :
    ‖maxTensorIn A B x‖ = maxTensorNorm x :=
  UniformSpace.Completion.norm_coe _

/-- **The cross-norm inside `A ⊗_max B`**: `‖a ⊗ₜ b‖ = ‖a‖ * ‖b‖`, so both
factors sit inside the maximal tensor product with their own norms. -/
theorem norm_maxTensorIn_tmul (a : A) (b : B) :
    ‖maxTensorIn A B (a ⊗ₜ[ℂ] b)‖ = ‖a‖ * ‖b‖ := by
  rw [norm_maxTensorIn, maxTensorNorm_tmul]

theorem maxTensorIn_injective :
    Function.Injective (maxTensorIn A B) := by
  intro x y hxy
  have hz : ‖maxTensorIn A B (x - y)‖ = 0 := by
    rw [map_sub, hxy, sub_self, norm_zero]
  rw [norm_maxTensorIn] at hz
  exact sub_eq_zero.mp (isCStarNorm_maxTensorNorm.eq_zero _ hz)

theorem denseRange_maxTensorIn :
    DenseRange (maxTensorIn A B) :=
  UniformSpace.Completion.denseRange_coe.comp
    (WithCStarNorm.retagStarAlgHom_surjective
      isCStarNorm_maxTensorNorm).denseRange
    (UniformSpace.Completion.continuous_coe _)

/-! ## The universal property

A pair of ⋆-homomorphisms out of the factors with commuting ranges factors
through `A ⊗_max B`, uniquely.  Contractivity of the pair is *not* a
hypothesis: a ⋆-homomorphism between C⋆-algebras is automatically contractive,
which is what puts the seminorm it induces into the family. -/

section UniversalProperty

variable {C : Type w} [CStarAlgebra C]

omit [Nontrivial A] [Nontrivial B] in
/-- The lift of a commuting pair to the algebraic tensor product commutes with
the involution.  On an elementary tensor the two sides are `f a⋆ · g b⋆` and
`(g b)⋆ · (f a)⋆`, which agree because the involution carries a commuting pair
to a commuting pair. -/
theorem tensorLift_star (f : A →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] C)
    (hfg : ∀ (a : A) (b : B), Commute (f a) (g b)) (x : A ⊗[ℂ] B) :
    Algebra.TensorProduct.lift f.toAlgHom g.toAlgHom hfg (star x)
      = star (Algebra.TensorProduct.lift f.toAlgHom g.toAlgHom hfg x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [star_zero, map_zero, star_zero]
  | tmul a b =>
      rw [TensorProduct.star_tmul, Algebra.TensorProduct.lift_tmul,
        Algebra.TensorProduct.lift_tmul, star_mul]
      show f (star a) * g (star b) = star (g b) * star (f a)
      rw [StarHomClass.map_star f a, StarHomClass.map_star g b]
      -- the involution carries a commuting pair to a commuting pair, and
      -- `Commute` unfolds to exactly this equation
      exact ((hfg a b).star_star).eq
  | add y z hy hz => rw [star_add, map_add, map_add, hy, hz, star_add]

/-- **A commuting pair of ⋆-homomorphisms, as a ⋆-homomorphism of the algebraic
tensor product.**  Mathlib's `Algebra.TensorProduct.lift` supplies the algebra
homomorphism; what is added is that it respects the involution. -/
noncomputable def tensorStarLift (f : A →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] C)
    (hfg : ∀ (a : A) (b : B), Commute (f a) (g b)) :
    (A ⊗[ℂ] B) →⋆ₐ[ℂ] C :=
  { Algebra.TensorProduct.lift f.toAlgHom g.toAlgHom hfg with
    map_star' := tensorLift_star f g hfg }

omit [Nontrivial A] [Nontrivial B] in
@[simp] theorem tensorStarLift_tmul (f : A →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] C)
    (hfg : ∀ (a : A) (b : B), Commute (f a) (g b)) (a : A) (b : B) :
    tensorStarLift f g hfg (a ⊗ₜ[ℂ] b) = f a * g b := rfl

omit [Nontrivial A] [Nontrivial B] in
/-- **The seminorm a commuting pair induces belongs to the family.**  Each
factor is contractive because a ⋆-homomorphism between C⋆-algebras is, so this
is where the universal property meets the supremum. -/
theorem isTensorCStarSeminorm_tensorStarLift (f : A →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] C)
    (hfg : ∀ (a : A) (b : B), Commute (f a) (g b)) :
    IsTensorCStarSeminorm (fun x ↦ ‖tensorStarLift f g hfg x‖) where
  isCStarSeminorm := isCStarSeminorm_norm.comp (tensorStarLift f g hfg)
  left_le a := by
    show ‖tensorStarLift f g hfg (a ⊗ₜ[ℂ] (1 : B))‖ ≤ ‖a‖
    rw [tensorStarLift_tmul, map_one, mul_one]
    exact NonUnitalStarAlgHom.norm_apply_le f a
  right_le b := by
    show ‖tensorStarLift f g hfg ((1 : A) ⊗ₜ[ℂ] b)‖ ≤ ‖b‖
    rw [tensorStarLift_tmul, map_one, one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le g b

theorem norm_tensorStarLift_le (f : A →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] C)
    (hfg : ∀ (a : A) (b : B), Commute (f a) (g b)) (y : MaxPreTensor A B) :
    ‖((tensorStarLift f g hfg).comp
        (WithCStarNorm.unretagStarAlgHom isCStarNorm_maxTensorNorm)) y‖ ≤ ‖y‖ :=
  le_maxTensorNorm (isTensorCStarSeminorm_tensorStarLift f g hfg) y

/-- **The factorisation through `A ⊗_max B`.**  The pair's seminorm is
dominated by the maximal norm, so the algebraic lift is contractive for it and
extends across the completion. -/
noncomputable def maxTensorLift (f : A →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] C)
    (hfg : ∀ (a : A) (b : B), Commute (f a) (g b)) :
    MaxTensorProduct A B →⋆ₐ[ℂ] C :=
  CStarCompletion.extendStarAlgHom
    ((tensorStarLift f g hfg).comp
      (WithCStarNorm.unretagStarAlgHom isCStarNorm_maxTensorNorm))
    (CStarCompletion.uniformContinuous_of_norm_le _ (norm_tensorStarLift_le f g hfg))

@[simp] theorem maxTensorLift_apply (f : A →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] C)
    (hfg : ∀ (a : A) (b : B), Commute (f a) (g b)) (x : A ⊗[ℂ] B) :
    maxTensorLift f g hfg (maxTensorIn A B x) = tensorStarLift f g hfg x :=
  CStarCompletion.extendStarAlgHom_coe
    ((tensorStarLift f g hfg).comp
      (WithCStarNorm.unretagStarAlgHom isCStarNorm_maxTensorNorm))
    (CStarCompletion.uniformContinuous_of_norm_le _ (norm_tensorStarLift_le f g hfg))
    (WithCStarNorm.retagStarAlgHom isCStarNorm_maxTensorNorm x)

theorem maxTensorLift_tmul (f : A →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] C)
    (hfg : ∀ (a : A) (b : B), Commute (f a) (g b)) (a : A) (b : B) :
    maxTensorLift f g hfg (maxTensorIn A B (a ⊗ₜ[ℂ] b)) = f a * g b := by
  rw [maxTensorLift_apply, tensorStarLift_tmul]

/-- A ⋆-homomorphism out of `A ⊗_max B` is continuous, being contractive. -/
theorem continuous_of_maxTensorProduct
    (Φ : MaxTensorProduct A B →⋆ₐ[ℂ] C) :
    Continuous (Φ : MaxTensorProduct A B → C) := by
  refine (LipschitzWith.mk_one fun x y ↦ ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le Φ (x - y)

/-- Two ⋆-homomorphisms out of `A ⊗_max B` that agree on the elementary tensors
are equal: the elementary tensors span the algebraic tensor product, which is
dense. -/
theorem maxTensorProduct_hom_ext (Φ Ψ : MaxTensorProduct A B →⋆ₐ[ℂ] C)
    (h : ∀ (a : A) (b : B),
      Φ (maxTensorIn A B (a ⊗ₜ[ℂ] b)) = Ψ (maxTensorIn A B (a ⊗ₜ[ℂ] b))) :
    Φ = Ψ := by
  have hall : ∀ x : A ⊗[ℂ] B, Φ (maxTensorIn A B x) = Ψ (maxTensorIn A B x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => exact h a b
    | add y z hy hz => simp only [map_add, hy, hz]
  have hfun : (Φ : MaxTensorProduct A B → C) = (Ψ : MaxTensorProduct A B → C) :=
    denseRange_maxTensorIn.equalizer (continuous_of_maxTensorProduct Φ)
      (continuous_of_maxTensorProduct Ψ) (funext hall)
  exact DFunLike.ext _ _ fun x ↦ congrFun hfun x

/-- **The universal property of `A ⊗_max B`.**  A pair of ⋆-homomorphisms out
of the factors whose ranges commute extends uniquely to `A ⊗_max B`.

The target is quantified at a universe independent of those of `A` and `B`:
the family the norm is the supremum of is indexed by seminorms on `A ⊙ B`, and
a seminorm knows nothing about where `C` lives. -/
theorem maxTensorProduct_existsUnique_lift (f : A →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] C)
    (hfg : ∀ (a : A) (b : B), Commute (f a) (g b)) :
    ∃! Φ : MaxTensorProduct A B →⋆ₐ[ℂ] C,
      ∀ (a : A) (b : B),
        Φ (maxTensorIn A B (a ⊗ₜ[ℂ] b)) = f a * g b := by
  refine ⟨maxTensorLift f g hfg, maxTensorLift_tmul f g hfg, ?_⟩
  intro Ψ hΨ
  refine maxTensorProduct_hom_ext Ψ _ fun a b ↦ ?_
  rw [hΨ a b, maxTensorLift_tmul]

end UniversalProperty

end CStarTensor
end GroupApproximation
