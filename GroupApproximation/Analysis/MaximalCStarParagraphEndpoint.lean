import GroupApproximation.Analysis.MaximalCStarLiteralBase
import GroupApproximation.Analysis.MaximalCStarProperCompression
import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import GroupApproximation.Analysis.ResiduallyFiniteDimensional
import GroupApproximation.Analysis.UniversalKazhdanCStarConsequences

/-!
# The maximal algebra under proper one-sided conjugation: the printed paragraph

This file is the paragraph-level endpoint for the manuscript remark *the
maximal algebra under proper one-sided conjugation*, which is
`\begin{remark}...\label{rem:maxinfinite}` inside the appendix
`\label{app:maxcstar}` of `non_mf_groups_exist.tex` — navigate by the label,
never by line number, since that file is under active concurrent edit.  The remark asserts, for a group
carrying a strict Kazhdan compression `t Γ t⁻¹ ⊊ Γ`, that

1. the Kazhdan projection `p_Γ` exists in the maximal algebra;
2. conjugation by `u_t` dominates it, on both sides;
3. the domination is strict, witnessed at the quasi-regular coordinate;
4. hence the maximal algebra is not stably finite,
5. carries no faithful trace,
6. and in particular is neither residually finite-dimensional
7. nor MF;
8. the assembly runs through the spectral projection of the averaged
   generator, whose spectral gap places the projection;
9. in contrast, the reduced algebra carries a faithful canonical trace and is
   finite, so it admits no such compression.

Items 1--5, 8 and 9 were already machine checked, in
`Analysis/MaximalCStarProperCompression`, `Analysis/QuasiRegularWitness` and
`Analysis/UniversalKazhdanCStarConsequences`.  Item 6 is supplied by
`Analysis/ResiduallyFiniteDimensional`.  Item 7 is supplied here.

## The MF clause

`HasMFEmbedding` is a faithful, possibly nonunital, ⋆-homomorphism into the
norm-matrix corona.  The obstruction is that *every isometry of the corona is
a unitary*: lifting an isometry to a bounded matrix sequence, its Gram defect
is null, so the finite-dimensional polar correction of
`Sofic/KazhdanCornerPolar` replaces it by a coordinatewise unitary sequence
without changing its class.  This is exactly the argument already used for
`unitaryCoronaToCStarCoronaUnitary_surjective`, which never uses more than
the isometry half of unitarity; it is reproved here from the isometry
hypothesis alone.  A possibly nonunital embedding `e` is handled by the
corner-complement correction `e s + (1 - e 1)`, the same device as
`nonUnitalStarAlgHomUnitaryMap` in `Analysis/MFAlgebra`.

## The badge declaration

`manuscriptMaximalCStarStrictCompressionRemark` collects all of the above
into a single statement about arbitrary strict Kazhdan compression data, and
then instantiates it at the remark's own example.

The remark names its instance in an aside the badge has to cover: *"the base of
`E` is such a pair"*.  That `E` is the literal eight-generator group of
Definition `def:E`, not the chosen presentation, and
`Sofic/ChosenMaximalCStarInfinite` instantiates the wrong one for this purpose
(a different group) and omits the residually finite-dimensional clause.  So the
second conjunct here exhibits `StrictKazhdanCompression Base MarkedGroup` for
the literal group --- built in `Analysis/MaximalCStarLiteralBase` --- and reads
off all seven printed conclusions at it, the RFD clause included, together with
the reduced-algebra contrast the remark closes on.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator ENNReal

noncomputable section

universe u w

/-- **Every isometry of the norm-matrix C⋆-corona is a unitary.**

Lift the isometry `x` to a bounded matrix sequence `a`.  Being an isometry
says exactly that the Gram defect `star a * a - 1` is a null sequence, so
cofinitely many coordinates have Gram defect at most `1/2`; at those
coordinates the finite-dimensional polar correction produces an exact unitary
matrix within `‖a‖ * (2 * defect)` of `a n`, and the identity is used in the
remaining finitely many coordinates.  The resulting coordinatewise unitary
sequence differs from `a` by a null sequence, hence has the same class `x`,
which is therefore unitary.

This is the argument of `unitaryCoronaToCStarCoronaUnitary_surjective`, which
uses only the isometry half of the unitarity hypothesis. -/
theorem normMatrixCStarCorona_mul_star_eq_one_of_star_mul_eq_one
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    {x : NormMatrixCStarCorona (fun n ↦ X n)}
    (hx : star x * x = 1) : x * star x = 1 := by
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
  have hgramZero :
      normMatrixCStarCoronaMk (fun n ↦ X n) (star a * a - 1) = 0 := by
    -- The additivity step is written out rather than rewritten with.  As a
    -- rewrite rule `map_sub` carries metavariable carriers, and the corona sits
    -- under `NormedRing`/`CStarAlgebra`, so the `SubtractionMonoidHomClass`
    -- query becomes a search over the whole instance graph.  Stated against a
    -- fully known proposition it is one determined lookup.
    have hsub : normMatrixCStarCoronaMk (fun n ↦ X n) (star a * a - 1)
        = normMatrixCStarCoronaMk (fun n ↦ X n) (star a * a)
          - normMatrixCStarCoronaMk (fun n ↦ X n) 1 :=
      map_sub (normMatrixCStarCoronaMk (fun n ↦ X n)) _ _
    have hone : normMatrixCStarCoronaMk (fun n ↦ X n) (star a * a)
        = normMatrixCStarCoronaMk (fun n ↦ X n) 1 := by
      rw [map_mul (normMatrixCStarCoronaMk (fun n ↦ X n)),
        map_one (normMatrixCStarCoronaMk (fun n ↦ X n))]
      simpa using hx
    rw [hsub, hone, sub_self]
  have hgram : IsNullMatrixSequence (fun n ↦ X n) cofinite (star a * a - 1) :=
    (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mp hgramZero
  have hgramTendsto :
      Tendsto (fun n ↦
        ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖) cofinite (nhds 0) := by
    simpa [IsNullMatrixSequence, KazhdanCornerMatrices.cornerGram,
      lp.star_apply, Matrix.star_eq_conjTranspose] using hgram
  have hgood : ∀ᶠ n in cofinite,
      ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ) := by
    have hnear := (Metric.tendsto_nhds.mp hgramTendsto)
      (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hnear] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  let u : ∀ n, Matrix.unitaryGroup (X n) ℂ := fun n ↦
    if hn : ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ) then
      KazhdanCornerMatrices.polarCorrectUnitary (a n)
        (KazhdanCornerMatrices.cornerGram_isHermitian (a n)) hn le_rfl
    else 1
  have hdiff : IsNullMatrixSequence (fun n ↦ X n) cofinite
      (unitarySequenceBounded X u - a) := by
    apply squeeze_zero'
      (Eventually.of_forall fun n ↦ norm_nonneg ((unitarySequenceBounded X u - a) n))
    · filter_upwards [hgood] with n hn
      change ‖(u n : Matrix (X n) (X n) ℂ) - a n‖ ≤
        ‖a‖ * (2 * ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖)
      rw [show u n = KazhdanCornerMatrices.polarCorrectUnitary (a n)
          (KazhdanCornerMatrices.cornerGram_isHermitian (a n)) hn le_rfl by
        rw [show u n = dite
            (‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ))
            (fun hn ↦ KazhdanCornerMatrices.polarCorrectUnitary (a n)
              (KazhdanCornerMatrices.cornerGram_isHermitian (a n)) hn le_rfl)
            (fun _ ↦ 1) by rfl, dif_pos hn]]
      exact (KazhdanCornerMatrices.norm_polarCorrect_sub_le_mul (a n)
        (KazhdanCornerMatrices.cornerGram_isHermitian (a n))
        (norm_nonneg _) hn le_rfl).trans
          (mul_le_mul_of_nonneg_right
            ((lp.isLUB_norm a).1 ⟨n, rfl⟩) (by positivity))
    · simpa only [mul_zero] using
        (hgramTendsto.const_mul 2).const_mul ‖a‖
  have hmk : normMatrixCStarCoronaMk (fun n ↦ X n) (unitarySequenceBounded X u)
      = normMatrixCStarCoronaMk (fun n ↦ X n) a := by
    have hsub : normMatrixCStarCoronaMk (fun n ↦ X n)
          (unitarySequenceBounded X u - a)
        = normMatrixCStarCoronaMk (fun n ↦ X n) (unitarySequenceBounded X u)
          - normMatrixCStarCoronaMk (fun n ↦ X n) a :=
      map_sub (normMatrixCStarCoronaMk (fun n ↦ X n)) _ _
    rw [← sub_eq_zero, ← hsub]
    exact (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mpr hdiff
  have hus : unitarySequenceBounded X u * star (unitarySequenceBounded X u) = 1 := by
    ext n i j
    exact congrArg (fun A : Matrix (X n) (X n) ℂ ↦ A i j)
      (Unitary.mul_star_self_of_mem (u n).property)
  rw [← hmk, normMatrixCStarCorona_star_mk, ← map_mul, hus, map_one]

namespace ProperProjectionCompression

variable {A : Type u} [CStarAlgebra A]

/-- **Proper compression obstructs MF.**  A faithful, possibly nonunital,
⋆-homomorphism `e` into a norm-matrix corona would send the proper isometry
`s` of the compression to `e s`, whose corner-complement correction
`e s + (1 - e 1)` is a genuine isometry of the corona.  Every isometry there
is a unitary, so `e (s * star s) = e 1`, and faithfulness would give
`s * star s = 1`, contradicting properness. -/
theorem not_hasMFEmbedding (D : ProperProjectionCompression A) :
    ¬ HasMFEmbedding A := by
  rintro ⟨X, hne, _hX, _hmono, e, he⟩
  letI : ∀ n, Nonempty (X n) := hne
  have hp_star : star (e 1) = e 1 := by rw [← map_star, star_one]
  have hp_mul : e 1 * e 1 = e 1 := by rw [← map_mul, one_mul]
  have hstarx : star (e D.isometry) = e (star D.isometry) :=
    (map_star e D.isometry).symm
  have hpx : e 1 * e D.isometry = e D.isometry := by rw [← map_mul, one_mul]
  have hxp : e D.isometry * e 1 = e D.isometry := by rw [← map_mul, mul_one]
  have hstarxp : star (e D.isometry) * e 1 = star (e D.isometry) := by
    rw [hstarx, ← map_mul, mul_one]
  have hpstarx : e 1 * star (e D.isometry) = star (e D.isometry) := by
    rw [hstarx, ← map_mul, one_mul]
  have hsx : star (e D.isometry) * e D.isometry = e 1 := by
    rw [hstarx, ← map_mul, D.star_isometry_mul_isometry]
  have hcompl : (1 - e 1) * (1 - e 1) = 1 - e 1 := by
    have hexp : (1 - e 1) * (1 - e 1) = 1 - e 1 - e 1 + e 1 * e 1 := by
      noncomm_ring
    rw [hexp, hp_mul]
    noncomm_ring
  have hz1 : star (e D.isometry) * (1 - e 1) = 0 := by
    have hexp : star (e D.isometry) * (1 - e 1)
        = star (e D.isometry) - star (e D.isometry) * e 1 := by noncomm_ring
    rw [hexp, hstarxp, sub_self]
  have hz2 : (1 - e 1) * e D.isometry = 0 := by
    have hexp : (1 - e 1) * e D.isometry
        = e D.isometry - e 1 * e D.isometry := by noncomm_ring
    rw [hexp, hpx, sub_self]
  have hz3 : e D.isometry * (1 - e 1) = 0 := by
    have hexp : e D.isometry * (1 - e 1)
        = e D.isometry - e D.isometry * e 1 := by noncomm_ring
    rw [hexp, hxp, sub_self]
  have hz4 : (1 - e 1) * star (e D.isometry) = 0 := by
    have hexp : (1 - e 1) * star (e D.isometry)
        = star (e D.isometry) - e 1 * star (e D.isometry) := by noncomm_ring
    rw [hexp, hpstarx, sub_self]
  have hstary : star (e D.isometry + (1 - e 1))
      = star (e D.isometry) + (1 - e 1) := by
    rw [star_add, star_sub, star_one, hp_star]
  have hiso : star (e D.isometry + (1 - e 1)) * (e D.isometry + (1 - e 1)) = 1 := by
    rw [hstary]
    have hexp : (star (e D.isometry) + (1 - e 1)) * (e D.isometry + (1 - e 1))
        = star (e D.isometry) * e D.isometry + star (e D.isometry) * (1 - e 1)
          + ((1 - e 1) * e D.isometry + (1 - e 1) * (1 - e 1)) := by
      noncomm_ring
    rw [hexp, hz1, hz2, hcompl, hsx]
    noncomm_ring
  have hunit := normMatrixCStarCorona_mul_star_eq_one_of_star_mul_eq_one X hiso
  rw [hstary] at hunit
  have hexp2 : (e D.isometry + (1 - e 1)) * (star (e D.isometry) + (1 - e 1))
      = e D.isometry * star (e D.isometry) + e D.isometry * (1 - e 1)
        + ((1 - e 1) * star (e D.isometry) + (1 - e 1) * (1 - e 1)) := by
    noncomm_ring
  rw [hexp2, hz3, hz4, hcompl, add_zero, zero_add] at hunit
  have hfinal : e D.isometry * star (e D.isometry) = e 1 := by
    have hsub := eq_sub_of_add_eq hunit
    rwa [sub_sub_cancel] at hsub
  have hmap : e (D.isometry * star D.isometry) = e 1 := by
    rw [map_mul, ← hstarx]
    exact hfinal
  exact D.isometry_mul_star_ne_one (he hmap)

/-- The same conclusion for the separability-carrying MF predicate. -/
theorem not_isMFAlgebra (D : ProperProjectionCompression A) : ¬ IsMFAlgebra A :=
  fun h ↦ D.not_hasMFEmbedding h.2

end ProperProjectionCompression

namespace MaximalCStarParagraphEndpoint

open MaximalCStarProperCompression

-- No section variables here.  The badged declaration quantifies over its group
-- arguments inside the proposition, and an in-scope `variable` of the same name
-- would make `scripts/check_non_mf_unconditional.py` read the elaborated type as
-- carrying a leading input the printed header does not show.

/-- **The printed remark, in full.**

The conjuncts follow the order of the printed sentences, for arbitrary
strict Kazhdan compression data over `E`:

* the Kazhdan projection `p_Γ` exists in the maximal algebra (self-adjoint
  and idempotent there);
* conjugation by `u_t` dominates it — the conjugate absorbs it on both
  sides;
* the domination is strict, the two projections differ;
* hence the maximal algebra is not Dedekind finite, not stably finite,
  carries no faithful tracial state, and in particular is neither
  residually finite-dimensional nor MF (in both the bare-embedding and the
  separable senses);
* the assembly: the spectral gap of the averaged generator places the
  projection, which the average then fixes;
* the contrast with Theorem D: the reduced algebra of the same group
  carries a faithful canonical trace and admits no proper compression at
  all, so its failure of MF is not a failure of finiteness.

The second conjunct is the remark's own aside — as of 2026-08-16 the remark
reads *"Let `G` contain a property-(T) subgroup `Γ` and an element `t` with
`t Γ t⁻¹ ⊊ Γ`; the base of `E` is such a pair"* — which is a claim about the
literal eight-generator group of Definition `def:E` and not about the chosen
presentation.  It is stated here
rather than left to a downstream file because the manuscript's badge is on this
declaration: a reader of the first conjunct alone learns what follows *from* a
strict Kazhdan compression, but not that the paper's own group has one.
`Analysis/MaximalCStarLiteralBase` builds the datum; every conclusion of the
first conjunct is then read off at it, including the residually
finite-dimensional clause.

This is the paragraph-level counterpart of the remark labelled
`rem:maxinfinite` in `non_mf_groups_exist.tex`. -/
theorem manuscriptMaximalCStarStrictCompressionRemark :
    (∀ {Γ : Type w} {E : Type u} [Group Γ] [Group E]
      (D : StrictKazhdanCompression Γ E),
    IsSelfAdjoint D.proj ∧
      D.proj * D.proj = D.proj ∧
      (D.shift * D.proj * star D.shift) * D.proj = D.proj ∧
      D.proj * (D.shift * D.proj * star D.shift) = D.proj ∧
      D.shift * D.proj * star D.shift ≠ D.proj ∧
      ¬ IsDedekindFiniteMonoid (MaximalGroupCStar E) ∧
      ¬ IsStablyFiniteRing (MaximalGroupCStar E) ∧
      ¬ Nonempty (FaithfulTracialState (MaximalGroupCStar E)) ∧
      ¬ IsResiduallyFiniteDimensional (MaximalGroupCStar E) ∧
      ¬ HasMFEmbedding (MaximalGroupCStar E) ∧
      ¬ IsMFAlgebra (MaximalGroupCStar E) ∧
      (∀ μ ∈ spectrum ℝ D.avg, μ ≤ D.rate ∨ μ = 1) ∧
      D.rate < 1 ∧
      D.avg * D.proj = D.proj ∧
      Nonempty (FaithfulTracialState
        (ReducedGroupCStarTrace.ReducedGroupCStar E)) ∧
      IsEmpty (ProperProjectionCompression
        (ReducedGroupCStarTrace.ReducedGroupCStar E))) ∧
    (Nonempty (StrictKazhdanCompression LiteralNonMFPresentation.Base
        LiteralNonMFPresentation.MarkedGroup) ∧
      ¬ IsDedekindFiniteMonoid
        (MaximalGroupCStar LiteralNonMFPresentation.MarkedGroup) ∧
      ¬ IsStablyFiniteRing
        (MaximalGroupCStar LiteralNonMFPresentation.MarkedGroup) ∧
      ¬ Nonempty (FaithfulTracialState
        (MaximalGroupCStar LiteralNonMFPresentation.MarkedGroup)) ∧
      ¬ IsResiduallyFiniteDimensional
        (MaximalGroupCStar LiteralNonMFPresentation.MarkedGroup) ∧
      ¬ HasMFEmbedding
        (MaximalGroupCStar LiteralNonMFPresentation.MarkedGroup) ∧
      ¬ IsMFAlgebra
        (MaximalGroupCStar LiteralNonMFPresentation.MarkedGroup) ∧
      Nonempty (FaithfulTracialState (ReducedGroupCStarTrace.ReducedGroupCStar
        LiteralNonMFPresentation.MarkedGroup)) ∧
      IsEmpty (ProperProjectionCompression
        (ReducedGroupCStarTrace.ReducedGroupCStar
          LiteralNonMFPresentation.MarkedGroup))) := by
  constructor
  · intro Γ E _ _ D
    exact
    ⟨D.isSelfAdjoint_proj, D.proj_mul_proj,
      D.conjugate_mul_proj, D.proj_mul_conjugate, D.conjugate_ne_proj,
      D.maximalCStar_not_isDedekindFiniteMonoid,
      D.maximalCStar_not_isStablyFiniteRing,
      D.maximalCStar_no_faithfulTracialState,
      D.toProperProjectionCompression.not_isResiduallyFiniteDimensional,
      D.toProperProjectionCompression.not_hasMFEmbedding,
      D.toProperProjectionCompression.not_isMFAlgebra,
      D.gap, D.rate_lt_one, D.avg_mul_proj,
      ⟨ReducedGroupCStarTrace.canonicalFaithfulTracialState E⟩,
      ReducedGroupCStarTrace.reduced_no_properProjectionCompression E⟩
  · obtain ⟨D⟩ := MaximalCStarLiteralBase.nonempty_strictCompression
    exact
    ⟨⟨D⟩,
      D.maximalCStar_not_isDedekindFiniteMonoid,
      D.maximalCStar_not_isStablyFiniteRing,
      D.maximalCStar_no_faithfulTracialState,
      D.toProperProjectionCompression.not_isResiduallyFiniteDimensional,
      D.toProperProjectionCompression.not_hasMFEmbedding,
      D.toProperProjectionCompression.not_isMFAlgebra,
      ⟨ReducedGroupCStarTrace.canonicalFaithfulTracialState _⟩,
      ReducedGroupCStarTrace.reduced_no_properProjectionCompression _⟩

end MaximalCStarParagraphEndpoint

end

end GroupApproximation
