import GroupApproximation.Analysis.NormMatrixCoronaUnitary

/-!
# The printed proof of the lifting lemma, step by step

`non_mf_groups_exist.tex`, `\begin{lemma}[lifting]unitary lifting result`, prints

> Every unitary `u ∈ 𝒬` lifts to a sequence of unitaries.

and proves it in one sentence with four moves:

> Lift `u` to a bounded sequence `(xₙ)`; unitarity of `q((xₙ))` gives
> `‖xₙ*xₙ − 1‖ → 0`.  Once `‖xₙ*xₙ − 1‖ ≤ 1/2`, the matrix `xₙ` is invertible
> and the polar correction `uₙ = xₙ(xₙ*xₙ)^{-1/2}` is unitary with
> `‖uₙ − xₙ‖ ≤ 2‖xₙ‖‖xₙ*xₙ − 1‖ → 0` by continuous functional calculus; set
> `uₙ = 1` at the finitely many remaining indices.

`Analysis/NormMatrixCoronaUnitary.unitaryCoronaToCStarCoronaUnitary_surjective`
walks that route, but inside a single proof body, so proof-ledger rows `PRE.09`
and `PRE.11` record that two of the four moves are not located anywhere:

* `PRE.09` — *"lift `u` to a bounded sequence"* and the unitarity defect it
  feeds.  Named here as `exists_boundedLift`, `gramDefect_tendsto_zero` and
  `coGramDefect_tendsto_zero`.  The manuscript prints only the first defect;
  unitarity in the corona is two equations and gives both, so both are stated,
  the printed one first.
* `PRE.11` — *"set `uₙ = 1` at the finitely many remaining indices"*.  What the
  printed sentence asserts is that this substitution does not move the class in
  the quotient.  That is `normMatrixCStarCoronaMk_eq_of_eventuallyEq` (in the
  C-star corona) and `quotientMk_eq_of_eventuallyEq` (in the unitary-sequence
  quotient): sequences agreeing off a finite set are identified.  Neither had a
  counterpart; the existing route never forms the finite exceptional set, it
  requires the estimate only on a member of the cofinite filter.

`polarPatch` is the printed sequence itself — polar correction where the Gram
defect is at most `1/2`, the identity elsewhere — as a named definition rather
than a `let` inside a proof, and `exists_boundedLift_polarPatch` is the unitary lifting result
routed through all four moves in the printed order, exposing the bounded lift,
the cofinite set on which the correction is defined, and the patched sequence.

The third move, the polar-correction estimate with the printed constant, is
`PrintedPreliminaryEstimates.manuscriptPolarCorrectionEstimate`; it is used
here through `KazhdanCornerMatrices.norm_polarCorrect_sub_le_mul`, the form
that carries the tolerance the filter argument needs.
-/

namespace GroupApproximation
namespace PrintedLiftingSteps

open Filter Matrix
open scoped Matrix.Norms.L2Operator ENNReal

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

noncomputable section

/-! ## `PRE.09`, first move: choose a bounded lift -/

/-- **"Lift `u` to a bounded sequence `(xₙ)`."**  The opening move of the
printed proof of the unitary lifting result, as a statement rather than a step: every element
of the corona — in particular every unitary of it — is the class of a
uniformly operator-norm-bounded sequence of matrices. -/
theorem exists_boundedLift (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    ∃ a : BoundedMatrixSequence (fun n ↦ X n),
      normMatrixCStarCoronaMk (fun n ↦ X n) a = x :=
  normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x

/-! ## `PRE.09`, second move: the asymptotic unitarity defects -/

/-- **"Unitarity of `q((xₙ))` gives `‖xₙ*xₙ − 1‖ → 0`."**  This is the printed
defect: the Gram defect of a bounded lift of a corona unitary is null along the
cofinite filter.  `KazhdanCornerMatrices.cornerGram (a n)` is `(aₙ)ᴴaₙ`. -/
theorem gramDefect_tendsto_zero
    {a : BoundedMatrixSequence (fun n ↦ X n)}
    (ha : star (normMatrixCStarCoronaMk (fun n ↦ X n) a) *
        normMatrixCStarCoronaMk (fun n ↦ X n) a = 1) :
    Tendsto (fun n ↦ ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖)
      cofinite (nhds 0) := by
  have hstar : star (normMatrixCStarCoronaMk (fun n ↦ X n) a)
      = normMatrixCStarCoronaMk (fun n ↦ X n) (star a) :=
    normMatrixCStarCorona_star_mk (fun n ↦ X n) a
  have hzero : normMatrixCStarCoronaMk (fun n ↦ X n) (star a * a - 1) = 0 := by
    rw [map_sub, map_mul, map_one, ← hstar]
    exact sub_eq_zero.mpr ha
  have hnull : IsNullMatrixSequence (fun n ↦ X n) cofinite (star a * a - 1) :=
    (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mp hzero
  simpa [IsNullMatrixSequence, KazhdanCornerMatrices.cornerGram,
    lp.star_apply, Matrix.star_eq_conjTranspose] using hnull

/-- The companion defect `‖xₙxₙ* − 1‖ → 0`.  The manuscript names only the
first, but membership in the unitary group of the corona is two equations, and
the second yields this one by the same computation. -/
theorem coGramDefect_tendsto_zero
    {a : BoundedMatrixSequence (fun n ↦ X n)}
    (ha : normMatrixCStarCoronaMk (fun n ↦ X n) a *
        star (normMatrixCStarCoronaMk (fun n ↦ X n) a) = 1) :
    Tendsto (fun n ↦ ‖a n * (a n)ᴴ - 1‖) cofinite (nhds 0) := by
  have hstar : star (normMatrixCStarCoronaMk (fun n ↦ X n) a)
      = normMatrixCStarCoronaMk (fun n ↦ X n) (star a) :=
    normMatrixCStarCorona_star_mk (fun n ↦ X n) a
  have hzero : normMatrixCStarCoronaMk (fun n ↦ X n) (a * star a - 1) = 0 := by
    rw [map_sub, map_mul, map_one, ← hstar]
    exact sub_eq_zero.mpr ha
  have hnull : IsNullMatrixSequence (fun n ↦ X n) cofinite (a * star a - 1) :=
    (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mp hzero
  simpa [IsNullMatrixSequence, lp.star_apply, Matrix.star_eq_conjTranspose]
    using hnull

/-! ## `PRE.11`: patching at finitely many indices does not move the class -/

/-- **The cofinite patch is invisible in the C-star corona.**  Two bounded
sequences that agree off a finite set have the same image under `q`.  This is
what the printed instruction *"set `uₙ = 1` at the finitely many remaining
indices"* relies on, and it is the reason that instruction costs nothing: the
patched sequence and the polar correction differ only there. -/
theorem normMatrixCStarCoronaMk_eq_of_eventuallyEq
    {a b : BoundedMatrixSequence (fun n ↦ X n)}
    (h : ∀ᶠ n in cofinite, a n = b n) :
    normMatrixCStarCoronaMk (fun n ↦ X n) a
      = normMatrixCStarCoronaMk (fun n ↦ X n) b := by
  rw [← sub_eq_zero, ← map_sub]
  refine (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mpr ?_
  show Tendsto (fun n ↦ ‖(a - b) n‖) cofinite (nhds 0)
  have key : (fun _ : ℕ ↦ (0 : ℝ)) =ᶠ[cofinite] fun n ↦ ‖(a - b) n‖ := by
    filter_upwards [h] with n hn
    show (0 : ℝ) = ‖(a - b) n‖
    have hn0 : (a - b) n = 0 := by
      show a n - b n = 0
      rw [hn, sub_self]
    rw [hn0, norm_zero]
  exact Tendsto.congr' key tendsto_const_nhds

omit [∀ n, Nonempty (X n)] in
/-- **The same patch in the unitary-sequence quotient.**  Two coordinatewise
unitary sequences that agree off a finite set have the same class in
`NormMatrixCoronaUnitary X`, because their quotient is eventually the identity
and so is null in operator length. -/
theorem quotientMk_eq_of_eventuallyEq
    {u v : ∀ n, Matrix.unitaryGroup (X n) ℂ}
    (h : ∀ᶠ n in cofinite, u n = v n) :
    (QuotientGroup.mk u : NormMatrixCoronaUnitary X) = QuotientGroup.mk v := by
  have hmem : u / v ∈ nullCofiniteOpSubgroup X := by
    show IsNullCofiniteOpSeq X (u / v)
    intro ε hε
    filter_upwards [h] with n hn
    have hone : (u / v) n = 1 := by
      show u n / v n = 1
      rw [hn, div_self']
    show opLength (X n) ((u / v) n) < ε
    rw [hone, opLength_one]
    exact hε
  have hquot : (QuotientGroup.mk (u / v) : NormMatrixCoronaUnitary X) = 1 :=
    (QuotientGroup.eq_one_iff (u / v)).mpr hmem
  have hdiv : (QuotientGroup.mk u : NormMatrixCoronaUnitary X) /
      QuotientGroup.mk v = 1 := hquot
  exact div_eq_one.mp hdiv

/-! ## The printed sequence, and the unitary lifting result routed through the four moves -/

/-- **The printed patched sequence.**  At an index where the Gram defect of the
chosen bounded lift is at most `1/2`, the coordinate is the printed polar
correction `xₙ(xₙ*xₙ)^{-1/2}`; at the finitely many remaining indices it is
`1`.  This is the `let` of `unitaryCoronaToCStarCoronaUnitary_surjective`,
promoted to a definition so the two branches can be named. -/
def polarPatch (a : BoundedMatrixSequence (fun n ↦ X n)) :
    ∀ n, Matrix.unitaryGroup (X n) ℂ := fun n ↦
  if hn : ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ) then
    KazhdanCornerMatrices.polarCorrectUnitary (a n)
      (KazhdanCornerMatrices.cornerGram_isHermitian (a n)) hn le_rfl
  else 1

omit [∀ n, Nonempty (X n)] in
/-- On the cofinite set where the Gram defect is at most `1/2`, the patched
sequence is the printed polar correction. -/
theorem polarPatch_eq_polarCorrect
    (a : BoundedMatrixSequence (fun n ↦ X n)) {n : ℕ}
    (hn : ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ)) :
    polarPatch X a n =
      KazhdanCornerMatrices.polarCorrectUnitary (a n)
        (KazhdanCornerMatrices.cornerGram_isHermitian (a n)) hn le_rfl := by
  rw [show polarPatch X a n
        = dite (‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ))
            (fun h ↦ KazhdanCornerMatrices.polarCorrectUnitary (a n)
              (KazhdanCornerMatrices.cornerGram_isHermitian (a n)) h le_rfl)
            (fun _ ↦ 1) from rfl]
  exact dif_pos hn

omit [∀ n, Nonempty (X n)] in
/-- **"Set `uₙ = 1` at the finitely many remaining indices."**  The other
branch, named. -/
theorem polarPatch_eq_one
    (a : BoundedMatrixSequence (fun n ↦ X n)) {n : ℕ}
    (hn : ¬ ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ)) :
    polarPatch X a n = 1 := by
  rw [show polarPatch X a n
        = dite (‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ))
            (fun h ↦ KazhdanCornerMatrices.polarCorrectUnitary (a n)
              (KazhdanCornerMatrices.cornerGram_isHermitian (a n)) h le_rfl)
            (fun _ ↦ 1) from rfl]
  exact dif_neg hn

/-- **the unitary lifting result, through the four printed moves.**  Every unitary of the
corona is `q((uₙ))` for the patched polar correction of some bounded lift.
The four conjuncts are the four moves of the printed sentence: `a` is the
bounded lift, the eventual bound is the Gram defect tending to zero, the
sequence `polarPatch X a` is the polar correction patched by `1` off that set,
and the last conjunct is that the class is nevertheless `x`. -/
theorem exists_boundedLift_polarPatch
    (x : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
    ∃ a : BoundedMatrixSequence (fun n ↦ X n),
      normMatrixCStarCoronaMk (fun n ↦ X n) a =
          (x : NormMatrixCStarCorona (fun n ↦ X n)) ∧
        (∀ᶠ n in cofinite,
          ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ)) ∧
        unitarySequenceToCorona X (polarPatch X a) = x := by
  obtain ⟨a, ha⟩ :=
    exists_boundedLift X (x : NormMatrixCStarCorona (fun n ↦ X n))
  have hunit : star (normMatrixCStarCoronaMk (fun n ↦ X n) a) *
      normMatrixCStarCoronaMk (fun n ↦ X n) a = 1 := by
    rw [ha]
    exact x.2.1
  have hgramTendsto := gramDefect_tendsto_zero X hunit
  have hgood : ∀ᶠ n in cofinite,
      ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ) := by
    have hnear := (Metric.tendsto_nhds.mp hgramTendsto) (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hnear] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  refine ⟨a, ha, hgood, ?_⟩
  have hdiff : IsNullMatrixSequence (fun n ↦ X n) cofinite
      (unitarySequenceBounded X (polarPatch X a) - a) := by
    apply squeeze_zero'
      (Eventually.of_forall fun n ↦
        norm_nonneg ((unitarySequenceBounded X (polarPatch X a) - a) n))
    · filter_upwards [hgood] with n hn
      change ‖(polarPatch X a n : Matrix (X n) (X n) ℂ) - a n‖ ≤
        ‖a‖ * (2 * ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖)
      rw [polarPatch_eq_polarCorrect X a hn]
      exact (KazhdanCornerMatrices.norm_polarCorrect_sub_le_mul (a n)
        (KazhdanCornerMatrices.cornerGram_isHermitian (a n))
        (norm_nonneg _) hn le_rfl).trans
          (mul_le_mul_of_nonneg_right
            ((lp.isLUB_norm a).1 ⟨n, rfl⟩) (by positivity))
    · simpa only [mul_zero] using
        (hgramTendsto.const_mul 2).const_mul ‖a‖
  apply Subtype.ext
  change normMatrixCStarCoronaMk (fun n ↦ X n)
      (unitarySequenceBounded X (polarPatch X a)) =
    (x : NormMatrixCStarCorona (fun n ↦ X n))
  rw [← ha, ← sub_eq_zero, ← map_sub]
  exact (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mpr hdiff

end

end PrintedLiftingSteps
end GroupApproximation
