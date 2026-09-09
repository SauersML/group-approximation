import GroupApproximation.Analysis.CStarMaxTensorQuotient
import GroupApproximation.Analysis.CStarIdealApproximateUnit
import GroupApproximation.Meta.AxiomGuard

/-!
# Maximal exactness: the kernel of `q ⊗_max id` is the closure of `I ⊙ C`

## The statement

For a closed star-stable two-sided ideal `I` of a C⋆-algebra `B` and any
C⋆-algebra `C`,

> `ker (q ⊗_max id : B ⊗_max C → (B ⧸ I) ⊗_max C) = closure (I ⊙ C)` ,

equivalently `(B ⧸ I) ⊗_max C = (B ⊗_max C) / closure(I ⊙ C)`.  One inclusion
is `CStarMaxTensorQuotient.idealMaxTensorSpan_subset_ker`; this module proves
the other, which is `IsMaxExactAt`.

## Why it is a universal-property argument and not an analytic one

The corresponding statement for `⊗_min` is *false* in general — it is exactness
of `C` — and its failure is what the notion of an exact C⋆-algebra is about.
For `⊗_max` it is a formality, because both sides solve the same universal
problem: a pair of ⋆-homomorphisms out of `B ⧸ I` and `C` with commuting
ranges is the same thing as a pair out of `B` and `C` with commuting ranges
whose first member kills `I`.

The proof below is that observation and nothing else.  Write `N` for the
closure of `I ⊙ C` inside `B ⊗_max C`.  It is a closed two-sided star-stable
ideal, so `(B ⊗_max C) ⧸ N` is a C⋆-algebra
(`Analysis/CStarIdealApproximateUnit`).  The pair

* `B ⧸ I → (B ⊗_max C) ⧸ N`, `b ↦ [b ⊗ 1]`, well defined because `I ⊙ C ⊆ N`,
* `C → (B ⊗_max C) ⧸ N`, `c ↦ [1 ⊗ c]`

has commuting ranges, so it factors through `(B ⧸ I) ⊗_max C`
(`maxTensorProduct_existsUnique_lift`), giving `Φ`.  Then `Φ ∘ (q ⊗_max id)`
and the quotient map `B ⊗_max C → (B ⊗_max C) ⧸ N` are two ⋆-homomorphisms out
of `B ⊗_max C` agreeing on elementary tensors, hence equal
(`maxTensorProduct_hom_ext`).  So a `z` killed by `q ⊗_max id` is killed by the
quotient map, i.e. lies in `N`.

## Where the work actually is

Not in the argument above, which is ten lines, but in exhibiting `N` as an
*ideal*: closure of a ℂ-span is only a ℂ-submodule, and absorbing
multiplication by an arbitrary element of the completion needs the density of
the algebraic tensor product twice over.  That bookkeeping is the first half of
this file.

## Relation to `Analysis/CStarSliceIdeal`

`CStarSliceIdeal.algIdealTensorSpan` is the same subspace of the algebraic
tensor product, and `algIdealTensor` below is deliberately not a rename of it:
that module states it for a `Submodule ℂ B` with the two factors in the **same
universe**, which the maximal tensor product does not require, and it develops
the slice-map side of the *minimal* exactness question rather than the ideal
structure of the *maximal* completion.  A later consolidation should keep one
of the two and restrict the scalars of the ideal; nothing here depends on which
survives.

## Manuscript status

Infrastructure.  It is step one of the route by which the manuscript's
`C^*_{\max}(W)` sentence becomes unconditional; on its own it certifies no
manuscript step.
-/

namespace GroupApproximation
namespace CStarTensor

open scoped TensorProduct

-- The section below fixes the ideal `I` together with its four hypotheses;
-- most individual lemmas use only some of them, and listing an `omit` on each
-- would be longer than the lemmas.
set_option linter.unusedSectionVars false

universe u v w

section MaxExact

variable {B : Type u} {C : Type w} [CStarAlgebra B] [CStarAlgebra C]
  [Nontrivial B] [Nontrivial C]
  (I : Ideal B) [I.IsTwoSided] [IsStarStable I] [IsClosed (I : Set B)]
  [Nontrivial (B ⧸ I)]

/-! ## `I ⊙ C` inside the algebraic tensor product -/

/-- The ℂ-span of `I ⊙ C` inside `B ⊗[ℂ] C`. -/
noncomputable def algIdealTensor : Submodule ℂ (B ⊗[ℂ] C) :=
  Submodule.span ℂ {y | ∃ b c, b ∈ I ∧ y = b ⊗ₜ[ℂ] c}

theorem tmul_mem_algIdealTensor {b : B} (hb : b ∈ I) (c : C) :
    (b ⊗ₜ[ℂ] c) ∈ algIdealTensor (C := C) I :=
  Submodule.subset_span ⟨b, c, hb, rfl⟩

/-- `I ⊙ C` absorbs left multiplication by an elementary tensor. -/
theorem tmul_mul_mem_algIdealTensor (a : B) (d : C) {y : B ⊗[ℂ] C}
    (hy : y ∈ algIdealTensor (C := C) I) :
    (a ⊗ₜ[ℂ] d) * y ∈ algIdealTensor (C := C) I := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨b, c, hb, rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact tmul_mem_algIdealTensor I (Ideal.mul_mem_left I a hb) _
  · rw [mul_zero]
    exact Submodule.zero_mem _
  · intro x z _ _ hx hz
    rw [mul_add]
    exact Submodule.add_mem _ hx hz
  · intro r x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ r hx

/-- `I ⊙ C` absorbs right multiplication by an elementary tensor. -/
theorem mul_tmul_mem_algIdealTensor (a : B) (d : C) {y : B ⊗[ℂ] C}
    (hy : y ∈ algIdealTensor (C := C) I) :
    y * (a ⊗ₜ[ℂ] d) ∈ algIdealTensor (C := C) I := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨b, c, hb, rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact tmul_mem_algIdealTensor I (Ideal.mul_mem_right a I hb) _
  · rw [zero_mul]
    exact Submodule.zero_mem _
  · intro x z _ _ hx hz
    rw [add_mul]
    exact Submodule.add_mem _ hx hz
  · intro r x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r hx

/-- `I ⊙ C` is star-stable. -/
theorem star_mem_algIdealTensor {y : B ⊗[ℂ] C}
    (hy : y ∈ algIdealTensor (C := C) I) :
    star y ∈ algIdealTensor (C := C) I := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨b, c, hb, rfl⟩
    rw [TensorProduct.star_tmul]
    exact tmul_mem_algIdealTensor I (IsStarStable.star_mem hb) _
  · rw [star_zero]
    exact Submodule.zero_mem _
  · intro x z _ _ hx hz
    rw [star_add]
    exact Submodule.add_mem _ hx hz
  · intro r x _ hx
    rw [star_smul]
    exact Submodule.smul_mem _ _ hx

/-! ## `N`, the closure of `I ⊙ C` inside `B ⊗_max C` -/

/-- The image of `I ⊙ C` inside `B ⊗_max C`, as a ℂ-submodule. -/
noncomputable def maxTensorIdealSpan : Submodule ℂ (MaxTensorProduct B C) :=
  (algIdealTensor (C := C) I).map (maxTensorIn B C : (B ⊗[ℂ] C) →ₗ[ℂ] _)

theorem maxTensorIn_mem_maxTensorIdealSpan {y : B ⊗[ℂ] C}
    (hy : y ∈ algIdealTensor (C := C) I) :
    maxTensorIn B C y ∈ maxTensorIdealSpan (C := C) I :=
  ⟨y, hy, rfl⟩

/-- `N`: the closure of the image of `I ⊙ C`, as a ℂ-submodule. -/
noncomputable def maxTensorIdealClosure : Submodule ℂ (MaxTensorProduct B C) :=
  (maxTensorIdealSpan (C := C) I).topologicalClosure

theorem isClosed_maxTensorIdealClosure :
    IsClosed ((maxTensorIdealClosure (C := C) I :
      Submodule ℂ (MaxTensorProduct B C)) : Set (MaxTensorProduct B C)) :=
  isClosed_closure

theorem mem_maxTensorIdealClosure_of_mem_span {z : MaxTensorProduct B C}
    (hz : z ∈ maxTensorIdealSpan (C := C) I) :
    z ∈ maxTensorIdealClosure (C := C) I :=
  (maxTensorIdealSpan (C := C) I).le_topologicalClosure hz

/-- Left multiplication by an arbitrary element of the completion keeps `N`
inside itself.  Two density arguments: first the multiplier is approximated by
algebraic tensors, then the multiplicand is. -/
theorem mul_mem_maxTensorIdealClosure (x : MaxTensorProduct B C)
    {z : MaxTensorProduct B C} (hz : z ∈ maxTensorIdealClosure (C := C) I) :
    x * z ∈ maxTensorIdealClosure (C := C) I := by
  -- the set of `w` with `x * w ∈ N`, for a fixed `x`, is closed
  have hclosedR : ∀ x : MaxTensorProduct B C,
      IsClosed {w : MaxTensorProduct B C |
        x * w ∈ maxTensorIdealClosure (C := C) I} := by
    intro x
    exact (isClosed_maxTensorIdealClosure (C := C) I).preimage
      (continuous_const.mul continuous_id)
  -- the set of `x` with `x * (image of a fixed algebraic ideal element) ∈ N`
  have hclosedL : ∀ y : B ⊗[ℂ] C,
      IsClosed {v : MaxTensorProduct B C |
        v * maxTensorIn B C y ∈ maxTensorIdealClosure (C := C) I} := by
    intro y
    exact (isClosed_maxTensorIdealClosure (C := C) I).preimage
      (continuous_id.mul continuous_const)
  -- step 1: an algebraic multiplier times an algebraic ideal element
  have hstep1 : ∀ (u : B ⊗[ℂ] C) {y : B ⊗[ℂ] C},
      y ∈ algIdealTensor (C := C) I →
      maxTensorIn B C u * maxTensorIn B C y ∈
        maxTensorIdealClosure (C := C) I := by
    intro u y hy
    rw [← map_mul]
    refine mem_maxTensorIdealClosure_of_mem_span I ?_
    refine maxTensorIn_mem_maxTensorIdealSpan I ?_
    induction u using TensorProduct.induction_on with
    | zero =>
        rw [zero_mul]
        exact Submodule.zero_mem _
    | tmul a d => exact tmul_mul_mem_algIdealTensor I a d hy
    | add p q hp hq =>
        rw [add_mul]
        exact Submodule.add_mem _ hp hq
  -- step 2: an arbitrary multiplier times an algebraic ideal element
  have hstep2 : ∀ (v : MaxTensorProduct B C) {y : B ⊗[ℂ] C},
      y ∈ algIdealTensor (C := C) I →
      v * maxTensorIn B C y ∈ maxTensorIdealClosure (C := C) I := by
    intro v y hy
    have hsub : Set.range (maxTensorIn B C) ⊆
        {w : MaxTensorProduct B C |
          w * maxTensorIn B C y ∈ maxTensorIdealClosure (C := C) I} := by
      rintro _ ⟨u, rfl⟩
      exact hstep1 u hy
    have huniv : (Set.univ : Set (MaxTensorProduct B C)) ⊆
        {w : MaxTensorProduct B C |
          w * maxTensorIn B C y ∈ maxTensorIdealClosure (C := C) I} := by
      rw [← (denseRange_maxTensorIn (A := B) (B := C)).closure_eq]
      exact (hclosedL y).closure_subset_iff.mpr hsub
    exact huniv (Set.mem_univ v)
  -- step 3: an arbitrary multiplier times an arbitrary element of `N`
  have hsub : (maxTensorIdealSpan (C := C) I : Set (MaxTensorProduct B C)) ⊆
      {w : MaxTensorProduct B C |
        x * w ∈ maxTensorIdealClosure (C := C) I} := by
    rintro _ ⟨y, hy, rfl⟩
    exact hstep2 x hy
  exact (hclosedR x).closure_subset_iff.mpr hsub hz

/-- Right multiplication, by the same two density arguments. -/
theorem mem_mul_maxTensorIdealClosure {z : MaxTensorProduct B C}
    (hz : z ∈ maxTensorIdealClosure (C := C) I) (x : MaxTensorProduct B C) :
    z * x ∈ maxTensorIdealClosure (C := C) I := by
  have hclosedL : ∀ x : MaxTensorProduct B C,
      IsClosed {w : MaxTensorProduct B C |
        w * x ∈ maxTensorIdealClosure (C := C) I} := by
    intro x
    exact (isClosed_maxTensorIdealClosure (C := C) I).preimage
      (continuous_id.mul continuous_const)
  have hclosedR : ∀ y : B ⊗[ℂ] C,
      IsClosed {v : MaxTensorProduct B C |
        maxTensorIn B C y * v ∈ maxTensorIdealClosure (C := C) I} := by
    intro y
    exact (isClosed_maxTensorIdealClosure (C := C) I).preimage
      (continuous_const.mul continuous_id)
  have hstep1 : ∀ (u : B ⊗[ℂ] C) {y : B ⊗[ℂ] C},
      y ∈ algIdealTensor (C := C) I →
      maxTensorIn B C y * maxTensorIn B C u ∈
        maxTensorIdealClosure (C := C) I := by
    intro u y hy
    rw [← map_mul]
    refine mem_maxTensorIdealClosure_of_mem_span I ?_
    refine maxTensorIn_mem_maxTensorIdealSpan I ?_
    induction u using TensorProduct.induction_on with
    | zero =>
        rw [mul_zero]
        exact Submodule.zero_mem _
    | tmul a d => exact mul_tmul_mem_algIdealTensor I a d hy
    | add p q hp hq =>
        rw [mul_add]
        exact Submodule.add_mem _ hp hq
  have hstep2 : ∀ (v : MaxTensorProduct B C) {y : B ⊗[ℂ] C},
      y ∈ algIdealTensor (C := C) I →
      maxTensorIn B C y * v ∈ maxTensorIdealClosure (C := C) I := by
    intro v y hy
    have hsub : Set.range (maxTensorIn B C) ⊆
        {w : MaxTensorProduct B C |
          maxTensorIn B C y * w ∈ maxTensorIdealClosure (C := C) I} := by
      rintro _ ⟨u, rfl⟩
      exact hstep1 u hy
    have huniv : (Set.univ : Set (MaxTensorProduct B C)) ⊆
        {w : MaxTensorProduct B C |
          maxTensorIn B C y * w ∈ maxTensorIdealClosure (C := C) I} := by
      rw [← (denseRange_maxTensorIn (A := B) (B := C)).closure_eq]
      exact (hclosedR y).closure_subset_iff.mpr hsub
    exact huniv (Set.mem_univ v)
  have hsub : (maxTensorIdealSpan (C := C) I : Set (MaxTensorProduct B C)) ⊆
      {w : MaxTensorProduct B C |
        w * x ∈ maxTensorIdealClosure (C := C) I} := by
    rintro _ ⟨y, hy, rfl⟩
    exact hstep2 x hy
  exact (hclosedL x).closure_subset_iff.mpr hsub hz

/-- `N` is star-stable. -/
theorem star_mem_maxTensorIdealClosure {z : MaxTensorProduct B C}
    (hz : z ∈ maxTensorIdealClosure (C := C) I) :
    star z ∈ maxTensorIdealClosure (C := C) I := by
  have hclosed : IsClosed {w : MaxTensorProduct B C |
      star w ∈ maxTensorIdealClosure (C := C) I} :=
    (isClosed_maxTensorIdealClosure (C := C) I).preimage continuous_star
  have hsub : (maxTensorIdealSpan (C := C) I : Set (MaxTensorProduct B C)) ⊆
      {w : MaxTensorProduct B C |
        star w ∈ maxTensorIdealClosure (C := C) I} := by
    rintro _ ⟨y, hy, rfl⟩
    show star (maxTensorIn B C y) ∈ maxTensorIdealClosure (C := C) I
    rw [← map_star]
    exact mem_maxTensorIdealClosure_of_mem_span I
      (maxTensorIn_mem_maxTensorIdealSpan I (star_mem_algIdealTensor I hy))
  exact hclosed.closure_subset_iff.mpr hsub hz

/-- `N` as an ideal of `B ⊗_max C`. -/
noncomputable def maxTensorIdeal : Ideal (MaxTensorProduct B C) where
  carrier := ((maxTensorIdealClosure (C := C) I :
    Submodule ℂ (MaxTensorProduct B C)) : Set (MaxTensorProduct B C))
  zero_mem' := Submodule.zero_mem _
  add_mem' := by
    intro a b ha hb
    exact Submodule.add_mem (maxTensorIdealClosure (C := C) I) ha hb
  smul_mem' := by
    intro r x hx
    exact mul_mem_maxTensorIdealClosure I r hx

@[simp] theorem mem_maxTensorIdeal_iff (z : MaxTensorProduct B C) :
    z ∈ maxTensorIdeal (C := C) I ↔ z ∈ maxTensorIdealClosure (C := C) I :=
  Iff.rfl

instance maxTensorIdeal_isTwoSided :
    (maxTensorIdeal (C := C) I).IsTwoSided :=
  ⟨fun b h ↦ mem_mul_maxTensorIdealClosure I h b⟩

instance maxTensorIdeal_isStarStable :
    IsStarStable (maxTensorIdeal (C := C) I) :=
  ⟨fun h ↦ star_mem_maxTensorIdealClosure I h⟩

instance maxTensorIdeal_isClosed :
    IsClosed ((maxTensorIdeal (C := C) I : Ideal (MaxTensorProduct B C)) :
      Set (MaxTensorProduct B C)) :=
  isClosed_maxTensorIdealClosure (C := C) I

/-! ## The two legs -/

/-- `B ⊗_max C` is nontrivial: its unit has norm one. -/
instance nontrivial_maxTensorProduct : Nontrivial (MaxTensorProduct B C) := by
  refine ⟨maxTensorIn B C ((1 : B) ⊗ₜ[ℂ] (1 : C)), 0, ?_⟩
  intro hcon
  have hn : ‖maxTensorIn B C ((1 : B) ⊗ₜ[ℂ] (1 : C))‖ = 1 := by
    rw [norm_maxTensorIn_tmul, CStarRing.norm_one, CStarRing.norm_one, mul_one]
  rw [hcon, norm_zero] at hn
  exact one_ne_zero hn.symm

variable (B C) in
/-- `b ↦ b ⊗ₜ 1`, as a ⋆-algebra homomorphism. -/
noncomputable def includeLeftStar : B →⋆ₐ[ℂ] (B ⊗[ℂ] C) where
  toFun b := b ⊗ₜ[ℂ] (1 : C)
  map_one' := rfl
  map_mul' b b' := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := TensorProduct.zero_tmul _ _
  map_add' b b' := TensorProduct.add_tmul _ _ _
  commutes' r := by
    show (algebraMap ℂ B r) ⊗ₜ[ℂ] (1 : C) = algebraMap ℂ (B ⊗[ℂ] C) r
    rw [Algebra.TensorProduct.algebraMap_apply]
  map_star' b := by
    show (star b) ⊗ₜ[ℂ] (1 : C) = star (b ⊗ₜ[ℂ] (1 : C))
    rw [TensorProduct.star_tmul, star_one]

variable (B C) in
/-- `c ↦ 1 ⊗ₜ c`, as a ⋆-algebra homomorphism. -/
noncomputable def includeRightStar : C →⋆ₐ[ℂ] (B ⊗[ℂ] C) where
  toFun c := (1 : B) ⊗ₜ[ℂ] c
  map_one' := rfl
  map_mul' c c' := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  map_zero' := TensorProduct.tmul_zero _ _
  map_add' c c' := TensorProduct.tmul_add _ _ _
  commutes' r := by
    show (1 : B) ⊗ₜ[ℂ] (algebraMap ℂ C r) = algebraMap ℂ (B ⊗[ℂ] C) r
    rw [Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_eq_smul_one (R := ℂ) (A := B) r,
      Algebra.algebraMap_eq_smul_one (R := ℂ) (A := C) r,
      TensorProduct.smul_tmul]
  map_star' c := by
    show (1 : B) ⊗ₜ[ℂ] (star c) = star ((1 : B) ⊗ₜ[ℂ] c)
    rw [TensorProduct.star_tmul, star_one]

/-! ## The comparison map, and exactness -/

/-- The quotient of `B ⊗_max C` by the closure of `I ⊙ C`. -/
noncomputable abbrev MaxTensorQuot : Type max u w :=
  MaxTensorProduct B C ⧸ maxTensorIdeal (C := C) I

/-- The left leg into the quotient: `b ↦ [b ⊗ 1]`. -/
noncomputable def leftLegQuot : B →⋆ₐ[ℂ] MaxTensorQuot (C := C) I :=
  ((quotientStarMk (maxTensorIdeal (C := C) I)).comp
    (maxTensorIn B C)).comp (includeLeftStar B C)

/-- The right leg into the quotient: `c ↦ [1 ⊗ c]`. -/
noncomputable def rightLegQuot : C →⋆ₐ[ℂ] MaxTensorQuot (C := C) I :=
  ((quotientStarMk (maxTensorIdeal (C := C) I)).comp
    (maxTensorIn B C)).comp (includeRightStar B C)

theorem leftLegQuot_apply (b : B) :
    leftLegQuot (C := C) I b
      = quotientStarMk (maxTensorIdeal (C := C) I)
          (maxTensorIn B C (b ⊗ₜ[ℂ] (1 : C))) := rfl

theorem rightLegQuot_apply (c : C) :
    rightLegQuot (C := C) I c
      = quotientStarMk (maxTensorIdeal (C := C) I)
          (maxTensorIn B C ((1 : B) ⊗ₜ[ℂ] c)) := rfl

/-- The left leg kills `I`, because `b ⊗ 1` with `b ∈ I` is a generator of the
ideal we quotiented by. -/
theorem leftLegQuot_eq_zero (b : B) (hb : b ∈ I) :
    leftLegQuot (C := C) I b = 0 := by
  rw [leftLegQuot_apply, quotientStarMk_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact mem_maxTensorIdealClosure_of_mem_span I
    (maxTensorIn_mem_maxTensorIdealSpan I (tmul_mem_algIdealTensor I hb _))

/-- The left leg, factored through `B ⧸ I`. -/
noncomputable def quotLeftLeg : (B ⧸ I) →⋆ₐ[ℂ] MaxTensorQuot (C := C) I :=
  quotientStarLift I (leftLegQuot (C := C) I) (leftLegQuot_eq_zero I)

theorem quotLeftLeg_mk (b : B) :
    quotLeftLeg (C := C) I (Ideal.Quotient.mk I b)
      = leftLegQuot (C := C) I b :=
  quotientStarLift_mk I _ _ b

/-- The two legs have commuting ranges: on elementary tensors the products
agree already in the algebraic tensor product. -/
theorem quotLeftLeg_commute (x : B ⧸ I) (c : C) :
    Commute (quotLeftLeg (C := C) I x) (rightLegQuot (C := C) I c) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotLeftLeg_mk, leftLegQuot_apply, rightLegQuot_apply]
  show _ * _ = _ * _
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  simp only [mul_one, one_mul]

/-- The comparison ⋆-homomorphism `(B ⧸ I) ⊗_max C → (B ⊗_max C) ⧸ N`. -/
noncomputable def maxExactCompare :
    MaxTensorProduct (B ⧸ I) C →⋆ₐ[ℂ] MaxTensorQuot (C := C) I :=
  maxTensorLift (quotLeftLeg (C := C) I) (rightLegQuot (C := C) I)
    (quotLeftLeg_commute I)

theorem maxExactCompare_tmul (b : B) (c : C) :
    maxExactCompare (C := C) I
        (maxTensorIn (B ⧸ I) C ((Ideal.Quotient.mk I b) ⊗ₜ[ℂ] c))
      = quotientStarMk (maxTensorIdeal (C := C) I)
          (maxTensorIn B C (b ⊗ₜ[ℂ] c)) := by
  rw [maxExactCompare, maxTensorLift_tmul, quotLeftLeg_mk, leftLegQuot_apply,
    rightLegQuot_apply, ← map_mul, ← map_mul,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp only [mul_one, one_mul]

/-- **The comparison map inverts the quotient map.**  Both sides are
⋆-homomorphisms out of `B ⊗_max C` and they agree on elementary tensors. -/
theorem maxExactCompare_comp :
    (maxExactCompare (C := C) I).comp (quotientMaxTensorMap (C := C) I)
      = quotientStarMk (maxTensorIdeal (C := C) I) := by
  refine maxTensorProduct_hom_ext _ _ fun b c ↦ ?_
  show maxExactCompare (C := C) I
      (quotientMaxTensorMap (C := C) I (maxTensorIn B C (b ⊗ₜ[ℂ] c))) = _
  rw [quotientMaxTensorMap_maxTensorIn, tensorStarAlgHomMap_apply,
    Algebra.TensorProduct.map_tmul]
  show maxExactCompare (C := C) I
      (maxTensorIn (B ⧸ I) C ((quotientStarMk I b) ⊗ₜ[ℂ]
        ((AlgHom.id ℂ C) c))) = _
  rw [quotientStarMk_apply, maxExactCompare_tmul]
  rfl

/-- **Maximal exactness.**  The kernel of `q ⊗_max id` is exactly the closure
of `I ⊙ C`. -/
theorem isMaxExactAt : IsMaxExactAt (C := C) I := by
  intro z hz
  have h := DFunLike.congr_fun (maxExactCompare_comp (C := C) I) z
  have hquot : quotientStarMk (maxTensorIdeal (C := C) I) z = 0 := by
    rw [← h]
    show maxExactCompare (C := C) I (quotientMaxTensorMap (C := C) I z) = 0
    rw [hz, map_zero]
  rw [quotientStarMk_apply, Ideal.Quotient.eq_zero_iff_mem] at hquot
  have hmem : z ∈ closure (maxTensorIdealSpan (C := C) I :
      Set (MaxTensorProduct B C)) := hquot
  -- the two spans have the same closure
  refine closure_mono ?_ hmem
  rintro _ ⟨y, hy, rfl⟩
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨b, c, hb, rfl⟩
    exact Submodule.subset_span ⟨b, c, hb, rfl⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro p q _ _ hp hq
    rw [map_add]
    exact Submodule.add_mem _ hp hq
  · intro r p _ hp
    rw [map_smul]
    exact Submodule.smul_mem _ r hp

end MaxExact

end CStarTensor
end GroupApproximation

open GroupApproximation.CStarTensor

#audit_axioms GroupApproximation.CStarTensor.isMaxExactAt
