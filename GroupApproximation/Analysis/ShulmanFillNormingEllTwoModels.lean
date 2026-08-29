import GroupApproximation.Analysis.EllTwoBlockFamily
import GroupApproximation.Analysis.ShulmanFillNormingCoronaMap
import GroupApproximation.Analysis.ShulmanFillNormingDCStar
import GroupApproximation.Analysis.ShulmanFillNormingDoubledFlip
import GroupApproximation.Analysis.ShulmanFillNormingMatrixFlatten

/-!
# The printed models: `𝒟` on `ℓ²`, and its doubling

`Analysis/EllTwoBlockFamily` proves `EllTwoBlockFamilyStatement`: isometries
`Jₙ : ℂⁿ → ℓ²` with `Jₙ* Jₙ = 1`, `‖Jₙ‖ ≤ 1` and `Jₙ Jₙ* → 1` strongly.
`Analysis/StarStrongBlockModel` turns that into the three clauses of Shulman's
`𝒟` — `blockIota`, `norm_blockIota_le`, `tendsto_blockIota_one`.  This module
takes the last step: it reindexes so that no model is empty, and identifies the
*doubled* models with matrix algebras, which is what
`Analysis/ShulmanFillNormingProductMF` needs to make `𝒟` MF-embeddable.

The reindexing is forced.  `EllTwoBlockFamilyStatement` is stated at `kₙ = n`,
so its zeroth model is `ℂ⁰`; `hasMFEmbedding_boundedMatrixSequence` wants every
model nonempty.  Shifting to `kₙ = n + 1` costs one `Filter.Tendsto.comp` with
`tendsto_add_atTop_nat 1` and changes nothing else.

The identification is one faithful move, touching no norm:

    `M₂(B(ℂ^{n+1}))` --(entrywise `toEuclideanCLM.symm`, flattened)-->
        `M_{Fin 2 × Fin (n+1)}` .

It is written out entrywise rather than composed from
`Analysis/ShulmanFillNormingMatrixFlatten.flattenHom` and `cStarMatrixMap`; the
docstring of `doubledToMatrix` says why the composition cannot elaborate.

`HasMFEmbedding` passes backward along any injective `*`-homomorphism, so only
injectivity is ever needed — the C-star norms of the three algebras never have
to be compared.

The import of `Analysis/ShulmanFillNormingDCStar` is what makes the last
statement typecheck: `HasMFEmbedding` asks its argument for
`NonUnitalCStarAlgebra`, and a star subalgebra of a C-star algebra carries one
only once completeness is supplied from closedness, which is what
`starStrongCStarAlgebra` does.  No order instance is needed for the doubled
models: `ContinuousLinearMap.instLoewnerPartialOrder` and
`ContinuousLinearMap.instStarOrderedRing` are global, so
`CStarMatrix.instCStarAlgebra` applies to `M₂(B(ℂ^{n+1}))` on its own.  The
L2 operator norm on `Matrix` is scoped, so `Matrix.Norms.L2Operator` has to be
opened here as well as in `Analysis/ShulmanFillNormingMatrixFlatten`; a scoped
instance opened there does not travel with the import, and neither does a
`local instance`, which is why the three `…ForFlatten` instances are re-enabled
by `attribute` rather than declared again — a second copy would make
`boundedMap`'s target a different type from the one
`hasMFEmbedding_boundedMatrixSequence` speaks about.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology StarStrong PolarLiftingGeneralCStar

open scoped Matrix.Norms.L2Operator

noncomputable section

section EllTwoModels

/-- The printed models, shifted so that none is empty. -/
abbrev ellTwoModel (n : ℕ) : FiniteModel :=
  ⟨Fin (n + 1), inferInstance, inferInstance⟩

instance nonempty_ellTwoModel (n : ℕ) : Nonempty (ellTwoModel n) :=
  inferInstanceAs (Nonempty (Fin (n + 1)))

/-- The coordinate algebras of the printed `𝒟`: the operators on `ℂ^{n+1}`. -/
abbrev EllTwoCoefficient (n : ℕ) : Type :=
  EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (n + 1))

/-- The doubled printed models as C-star algebras, pinned once.  Left to the
instance search, this is rederived at every mention: `M₂` over `B(ℂ^{n+1})`
reaches `CStarAlgebra` through `CStarMatrix.instCStarAlgebra`, which wants the
Loewner order and the continuous functional calculus on the operators, and
running that inside a statement about `𝒟` exhausts the instance budget. -/
noncomputable local instance cStarAlgebraDoubledEllTwo (m : ℕ) :
    CStarAlgebra (DoubledModel EllTwoCoefficient m) := inferInstance

variable (J : ∀ n : ℕ, EuclideanSpace ℂ (Fin n) →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2)
  (hJ : ∀ (n : ℕ) (v : EuclideanSpace ℂ (Fin n)),
    (ContinuousLinearMap.adjoint (J n)) (J n v) = v)

/-- The shifted family. -/
def shiftedJ (n : ℕ) :
    EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] lp (fun _ : ℕ ↦ ℂ) 2 :=
  J (n + 1)

include hJ in
theorem shiftedJ_isometry (n : ℕ) (v : EuclideanSpace ℂ (Fin (n + 1))) :
    (ContinuousLinearMap.adjoint (shiftedJ J n)) (shiftedJ J n v) = v :=
  hJ (n + 1) v

theorem shiftedJ_norm_le (hJnorm : ∀ n, ‖J n‖ ≤ 1) (n : ℕ) :
    ‖shiftedJ J n‖ ≤ 1 :=
  hJnorm (n + 1)

/-- Shifting preserves the strong convergence of the range projections: it is
the original convergence composed with `n ↦ n + 1`. -/
theorem shiftedJ_tendsto
    (hP : ∀ v : lp (fun _ : ℕ ↦ ℂ) 2,
      Tendsto (fun n ↦ (J n) ((ContinuousLinearMap.adjoint (J n)) v))
        atTop (𝓝 v))
    (v : lp (fun _ : ℕ ↦ ℂ) 2) :
    Tendsto (fun n ↦ (shiftedJ J n)
        ((ContinuousLinearMap.adjoint (shiftedJ J n)) v)) atTop (𝓝 v) :=
  (hP v).comp (tendsto_add_atTop_nat 1)

end EllTwoModels

/-! ## The doubled models are matrix algebras -/

section DoubledMatrix

variable (n : ℕ)

-- The three instances `Analysis/ShulmanFillNormingMatrixFlatten` declares
-- locally are adopted rather than rebuilt: `boundedMap` below needs the
-- flattened matrix algebras to be C-star algebras, and a second copy of that
-- instance would make its target a different type from the one
-- `hasMFEmbedding_boundedMatrixSequence` speaks about.
attribute [local instance] matrixCStarAlgebraForFlatten
attribute [local instance] partialOrderMatrixForFlatten
attribute [local instance] starOrderedRingMatrixForFlatten

/-- The coefficient algebra as a matrix algebra: `toEuclideanCLM` backwards. -/
def coefficientToMatrix :
    EllTwoCoefficient n →⋆ₐ[ℂ] Matrix (ellTwoModel n) (ellTwoModel n) ℂ :=
  (Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ)).symm.toStarAlgHom

theorem coefficientToMatrix_injective :
    Function.Injective (coefficientToMatrix n) :=
  (Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℂ)).symm.injective

/-- **The doubled printed model is a matrix algebra.**  `toEuclideanCLM.symm`
entrywise and the flattening, done in one step rather than composed.

Composing them is what the obvious reading suggests, and it does not elaborate.
`cStarMatrixMap` carries only `[CStarAlgebra A] [CStarAlgebra B]`, so the
`Semiring B` in the type of its argument is the one reached through
`CStarAlgebra B`, whereas `coefficientToMatrix`'s target carries `Matrix`'s own
`Matrix.instSemiring`.  The two agree, but only after unfolding
`CStarAlgebra → NormedRing → Ring → Semiring`, and asking the unifier to do
that inside the doubly nested `CStarMatrix (Fin 2) (Fin 2) (Matrix …)` that the
composition's middle type would be exhausts the heartbeat budget.  Written
entrywise, that type never appears: the source is `M₂` over the operators,
whose structure comes from `CStarMatrix.instCStarAlgebra` alone, and the target
is a plain `Matrix`.  `coefficientToMatrix` is only ever applied to elements
here, never unified against another homomorphism type. -/
def doubledToMatrix :
    CStarMatrix (Fin 2) (Fin 2) (EllTwoCoefficient n) →⋆ₐ[ℂ]
      Matrix (flatDoubleModel (ellTwoModel n))
        (flatDoubleModel (ellTwoModel n)) ℂ where
  toFun X := fun p q ↦ coefficientToMatrix n (X p.1 q.1) p.2 q.2
  map_one' := by
    ext p q
    show coefficientToMatrix n
      ((1 : CStarMatrix (Fin 2) (Fin 2) (EllTwoCoefficient n)) p.1 q.1)
        p.2 q.2 = _
    by_cases h1 : p.1 = q.1
    · by_cases h2 : p.2 = q.2
      · have hpq : p = q := Prod.ext h1 h2
        rw [hpq, CStarMatrix.one_apply_eq, map_one]
        simp
      · have hpq : p ≠ q := fun h ↦ h2 (congrArg Prod.snd h)
        rw [h1, CStarMatrix.one_apply_eq, map_one, Matrix.one_apply_ne h2,
          Matrix.one_apply_ne hpq]
    · have hpq : p ≠ q := fun h ↦ h1 (congrArg Prod.fst h)
      rw [CStarMatrix.one_apply_ne h1, map_zero, Matrix.zero_apply,
        Matrix.one_apply_ne hpq]
  map_mul' X Z := by
    ext p q
    show coefficientToMatrix n ((X * Z) p.1 q.1) p.2 q.2 = _
    rw [CStarMatrix.mul_apply, map_sum, Matrix.sum_apply, Matrix.mul_apply]
    have hL : ∑ k : Fin 2,
        (coefficientToMatrix n (X p.1 k * Z k q.1)) p.2 q.2 =
        ∑ k : Fin 2, ∑ m : ellTwoModel n,
          coefficientToMatrix n (X p.1 k) p.2 m *
            coefficientToMatrix n (Z k q.1) m q.2 := by
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_mul, Matrix.mul_apply]
    have hR : ∑ j : Fin 2 × ellTwoModel n,
        coefficientToMatrix n (X p.1 j.1) p.2 j.2 *
          coefficientToMatrix n (Z j.1 q.1) j.2 q.2
        = ∑ k : Fin 2, ∑ m : ellTwoModel n,
            coefficientToMatrix n (X p.1 k) p.2 m *
              coefficientToMatrix n (Z k q.1) m q.2 :=
      Fintype.sum_prod_type' (fun k m ↦
        coefficientToMatrix n (X p.1 k) p.2 m *
          coefficientToMatrix n (Z k q.1) m q.2)
    rw [hL]
    exact hR.symm
  map_zero' := by
    ext p q
    show coefficientToMatrix n
      ((0 : CStarMatrix (Fin 2) (Fin 2) (EllTwoCoefficient n)) p.1 q.1)
        p.2 q.2 = _
    rw [CStarMatrix.zero_apply, map_zero, Matrix.zero_apply, Matrix.zero_apply]
  map_add' X Z := by
    ext p q
    show coefficientToMatrix n ((X + Z) p.1 q.1) p.2 q.2 = _
    rw [CStarMatrix.add_apply, map_add, Matrix.add_apply, Matrix.add_apply]
  commutes' z := by
    ext p q
    show coefficientToMatrix n
      ((algebraMap ℂ (CStarMatrix (Fin 2) (Fin 2) (EllTwoCoefficient n)) z)
        p.1 q.1) p.2 q.2 = _
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      CStarMatrix.smul_apply, map_smul, Matrix.smul_apply, Matrix.smul_apply]
    by_cases h1 : p.1 = q.1
    · by_cases h2 : p.2 = q.2
      · have hpq : p = q := Prod.ext h1 h2
        rw [hpq, CStarMatrix.one_apply_eq, map_one]
        simp
      · have hpq : p ≠ q := fun h ↦ h2 (congrArg Prod.snd h)
        rw [h1, CStarMatrix.one_apply_eq, map_one, Matrix.one_apply_ne h2,
          Matrix.one_apply_ne hpq]
    · have hpq : p ≠ q := fun h ↦ h1 (congrArg Prod.fst h)
      rw [CStarMatrix.one_apply_ne h1, map_zero, Matrix.zero_apply,
        Matrix.one_apply_ne hpq]
  map_star' X := by
    ext p q
    show coefficientToMatrix n ((star X) p.1 q.1) p.2 q.2 = _
    rw [CStarMatrix.star_apply, map_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply]

@[simp] theorem doubledToMatrix_apply
    (X : CStarMatrix (Fin 2) (Fin 2) (EllTwoCoefficient n))
    (p q : flatDoubleModel (ellTwoModel n)) :
    doubledToMatrix n X p q = coefficientToMatrix n (X p.1 q.1) p.2 q.2 := rfl

theorem doubledToMatrix_injective :
    Function.Injective (doubledToMatrix n) := by
  intro X Z h
  -- `ext i j` would not stop at the matrix indices: the entries are operators,
  -- so it goes on through `ContinuousLinearMap.ext` and `PiLp.ext` and leaves a
  -- scalar equation, which `coefficientToMatrix_injective` cannot meet.
  refine CStarMatrix.ext fun i j ↦ ?_
  apply coefficientToMatrix_injective n
  ext a b
  exact congrFun (congrFun h (i, a)) (j, b)

/-- **The bounded product of the doubled printed models is MF-embeddable.**
Flatten every coordinate to a matrix algebra, then apply the prefix
block-diagonal embedding of `Analysis/ShulmanFillNormingProductMF`. -/
theorem hasMFEmbedding_doubledEllTwoProduct
    [∀ m, Nontrivial (DoubledModel EllTwoCoefficient m)] :
    HasMFEmbedding
      (BoundedCStarSequence (fun n ↦ DoubledModel EllTwoCoefficient n)) :=
  (hasMFEmbedding_boundedMatrixSequence
      (fun n ↦ flatDoubleModel (ellTwoModel n))).of_injective_nonUnitalStarAlgHom
    (boundedMap (fun n ↦ doubledToMatrix n)).toNonUnitalStarAlgHom
    (boundedMap_injective (fun n ↦ doubledToMatrix n)
      (fun n ↦ doubledToMatrix_injective n))

/-- The doubled `𝒟` at the printed models as a C-star algebra, pinned.  Left to
the search, the goal's head is a `StarSubalgebra` coercion, so every candidate
instance is unified through it and against the doubled coefficient tower, and
the budget goes before `starStrongCStarAlgebra` is reached.  Named here, it is
a lookup. -/
noncomputable local instance cStarAlgebraDoubledEllTwoStarStrong
    [∀ m, Nontrivial (DoubledModel EllTwoCoefficient m)]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ι : ∀ n, DoubledModel EllTwoCoefficient n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : DoubledModel EllTwoCoefficient n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto
      (fun n ↦ ι n (1 : DoubledModel EllTwoCoefficient n) v) atTop (𝓝 v)) :
    CStarAlgebra (StarStrong.starStrongSubalgebra ι hnorm hone) :=
  starStrongCStarAlgebra ι hnorm hone

/-- The same, in the class `HasMFEmbedding` actually asks for.  Pinning only the
unital form is not enough: the search still has to walk
`CStarAlgebra → NonUnitalCStarAlgebra` with the `StarSubalgebra` coercion at the
head of the goal, and that is where the budget went. -/
noncomputable local instance nonUnitalCStarAlgebraDoubledEllTwoStarStrong
    [∀ m, Nontrivial (DoubledModel EllTwoCoefficient m)]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ι : ∀ n, DoubledModel EllTwoCoefficient n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : DoubledModel EllTwoCoefficient n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto
      (fun n ↦ ι n (1 : DoubledModel EllTwoCoefficient n) v) atTop (𝓝 v)) :
    NonUnitalCStarAlgebra (StarStrong.starStrongSubalgebra ι hnorm hone) :=
  -- Written out rather than `inferInstance`: the search this replaces is the
  -- one that overran, and `synthInstance.maxHeartbeats` is 20000 wherever it
  -- runs, so deferring it to this declaration would not have helped.
  @CStarAlgebra.toNonUnitalCStarAlgebra _
    (cStarAlgebraDoubledEllTwoStarStrong ι hnorm hone)

/-- **`𝒟` at the doubled printed models is MF-embeddable**, which is the `hD`
hypothesis of `ShulmanFill.isMFAlgebra_amalgam_of_glue`.  `𝒟` is a subalgebra
of the bounded product, and `HasMFEmbedding` passes backward along the
inclusion. -/
theorem hasMFEmbedding_doubledEllTwoStarStrong
    [∀ m, Nontrivial (DoubledModel EllTwoCoefficient m)]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ι : ∀ n, DoubledModel EllTwoCoefficient n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : DoubledModel EllTwoCoefficient n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto
      (fun n ↦ ι n (1 : DoubledModel EllTwoCoefficient n) v) atTop (𝓝 v)) :
    HasMFEmbedding (StarStrong.starStrongSubalgebra ι hnorm hone) :=
  hasMFEmbedding_doubledEllTwoProduct.of_injective_nonUnitalStarAlgHom
    (StarStrong.starStrongSubalgebra ι hnorm hone).subtype.toNonUnitalStarAlgHom
    fun _ _ h ↦ Subtype.ext h

end DoubledMatrix

end

end ShulmanFill
end GroupApproximation
