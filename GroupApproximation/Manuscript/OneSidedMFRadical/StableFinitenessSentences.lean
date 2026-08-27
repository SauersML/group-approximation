import GroupApproximation.Analysis.FiniteCStarMurrayVonNeumann
import GroupApproximation.Analysis.MatrixCoronaDedekindFinite
import GroupApproximation.Manuscript.OneSidedMFRadical.StableFinitenessSentencesCore
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Sentence-level formalization of the proof of `lem:stable-finite`

`non_mf_groups_exist.tex`, Lemma `lem:stable-finite` (tex lines 560-597), is
already formalized whole in
`Manuscript/OneSidedMFRadical/StableFiniteness.lean`
(`manuscriptNormMatrixCoronaStableFinite`).  This file gives one Lean
declaration to each printed *proof sentence* (proof at tex lines 581-596),
following the printed dependency order, so that every sentence of the proof
-- not only its statement -- has a 1:1 Lean counterpart.

The printed proof is a concrete argument (lift, polar-correct, patch,
amplify, then compare in a finite corner), distinct from the abstract
Neumann-series / Murray-von-Neumann route that
`manuscriptNormMatrixCoronaStableFinite` itself uses.  The concrete route is
assembled generically in `StableFinitenessSentencesCore.lean`, reusing
`Sofic/KazhdanCornerPolar.lean` and
`Manuscript/OneSidedMFRadical/SentenceStableFiniteProofClosure.lean`; this
file specializes that engine to the corona `A` fixed by the lemma statement,
one sentence at a time.

Proof-ledger keys (from the sentence census, tex lines 581-588), in printed
order:

* `fc6ea69c0036` -- "Write `A` for the displayed corona."
* `8461ba613634` -- "Suppose that `v^*v=1` in `A`, and let `(x_n)` be a
  bounded lift of `v`."
* `0ac3ff393cfe` -- "Then `‖x_n^*x_n-1‖→0`."
* `fc7ae023c534` -- "For all sufficiently large `n`, the matrix `x_n^*x_n`
  is invertible, and"
* `974e2b57e3ef` -- "[`u_n=x_n(x_n^*x_n)^{-1/2}`] is unitary."
* `ee3d6cbf975d` -- "Moreover, `‖u_n-x_n‖→0`; after assigning arbitrary
  unitary values to the finitely many remaining coordinates, `(u_n)` is a
  unitary lift of `v`."
* `b21cf7f0f627` -- "So `vv^*=1`, and `A` is finite."
* `993df6a79c44` -- "For every `k≥1`, apply this construction with matrix
  sizes `km_n` to see that `∏_nM_{km_n}(ℂ)/⊕_nM_{km_n}(ℂ)` is finite."
* `36cd63cf2803` -- "This corona is canonically isomorphic to `M_k(A)`, so
  `A` is stably finite."
* `9b9e5b396d6f` -- "Finally, let `p≤q` be equivalent projections in a
  stably finite algebra `B`, and choose a partial isometry `w` with
  `w^*w=q` and `ww^*=p`."
* `70c4de929477` -- "Then `w∈qBq` is an isometry in the finite corner
  `qBq`, so `p=ww^*=q`."
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **Proof sentence `fc6ea69c0036`.**  "Write `A` for the displayed
corona." -/
abbrev stableFiniteCorona (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    Type :=
  NormMatrixCStarCorona (fun n ↦ (X n : Type))

/-- **Proof sentence `8461ba613634`.**  "Suppose that `v^*v=1` in `A`, and
let `(x_n)` be a bounded lift of `v`." -/
theorem sentence_8461ba613634 (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    {v : stableFiniteCorona X} (_hv : star v * v = 1) :
    ∃ x : BoundedMatrixSequence (fun n ↦ (X n : Type)),
      normMatrixCStarCoronaMk (fun n ↦ (X n : Type)) x = v :=
  normMatrixCStarCoronaMk_surjective (fun n ↦ (X n : Type)) v

/-- **Proof sentence `0ac3ff393cfe`.**  "Then `‖x_n^*x_n-1‖→0`." -/
theorem sentence_0ac3ff393cfe (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    {v : stableFiniteCorona X} (hv : star v * v = 1)
    {x : BoundedMatrixSequence (fun n ↦ (X n : Type))}
    (hx : normMatrixCStarCoronaMk (fun n ↦ (X n : Type)) x = v) :
    Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) cofinite (nhds 0) :=
  manuscriptStableFiniteBoundedLiftGramDefect (fun n ↦ (X n : Type)) v x hx hv

/-- **Proof sentence `fc7ae023c534`.**  "For all sufficiently large `n`,
the matrix `x_n^*x_n` is invertible, and" -/
theorem sentence_fc7ae023c534 (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    {x : BoundedMatrixSequence (fun n ↦ (X n : Type))}
    (hgram : Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) cofinite (nhds 0)) :
    ∀ᶠ n in cofinite, IsUnit (star (x n) * x n) := by
  have hgram' : Tendsto
      (fun n ↦ ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖) cofinite
      (nhds 0) := by
    simpa only [StableFinitenessSentencesCore.cornerGram_eq_star_mul_self]
      using hgram
  have hgood : ∀ᶠ n in cofinite,
      ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖ ≤ (1 / 2 : ℝ) := by
    have hnear := (Metric.tendsto_nhds.mp hgram') (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hnear] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  filter_upwards [hgood] with n hn
  rw [← StableFinitenessSentencesCore.cornerGram_eq_star_mul_self]
  exact StableFinitenessSentencesCore.isUnit_cornerGram_of_eigenvalues_pos
    (x n) (KazhdanCornerMatrices.cornerGram_isHermitian (x n))
    (KazhdanCornerMatrices.cornerGram_eigenvalues_pos_of_norm_sub_one_le
      (x n) (KazhdanCornerMatrices.cornerGram_isHermitian (x n)) hn le_rfl)

/-- **Proof sentence `974e2b57e3ef`.**  "[`u_n=x_n(x_n^*x_n)^{-1/2}`] is
unitary." -/
theorem sentence_974e2b57e3ef (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    {x : BoundedMatrixSequence (fun n ↦ (X n : Type))} {n : ℕ}
    (hn : ‖star (x n) * x n - 1‖ ≤ (1 / 2 : ℝ)) :
    KazhdanCornerMatrices.polarCorrect (x n)
        (KazhdanCornerMatrices.cornerGram_isHermitian (x n)) ∈
      Matrix.unitaryGroup (X n) ℂ := by
  have hn' : ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖ ≤ (1 / 2 : ℝ) := by
    rwa [StableFinitenessSentencesCore.cornerGram_eq_star_mul_self]
  exact KazhdanCornerMatrices.polarCorrect_mem_unitaryGroup (x n)
    (KazhdanCornerMatrices.cornerGram_isHermitian (x n))
    (KazhdanCornerMatrices.cornerGram_eigenvalues_pos_of_norm_sub_one_le
      (x n) (KazhdanCornerMatrices.cornerGram_isHermitian (x n)) hn' le_rfl)

/-- **Proof sentence `ee3d6cbf975d`.**  "Moreover, `‖u_n-x_n‖→0`; after
assigning arbitrary unitary values to the finitely many remaining
coordinates, `(u_n)` is a unitary lift of `v`." -/
theorem sentence_ee3d6cbf975d (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    {v : stableFiniteCorona X} (_hv : star v * v = 1)
    {x : BoundedMatrixSequence (fun n ↦ (X n : Type))}
    (hx : normMatrixCStarCoronaMk (fun n ↦ (X n : Type)) x = v)
    (hgram : Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) cofinite (nhds 0)) :
    Tendsto
        (fun n ↦ ‖StableFinitenessSentencesCore.polarPatch x n - x n‖)
        cofinite (nhds 0) ∧
      normMatrixCStarCoronaMk (fun n ↦ (X n : Type))
          (StableFinitenessSentencesCore.polarPatchSeq x) = v := by
  have hgram' : Tendsto
      (fun n ↦ ‖KazhdanCornerMatrices.cornerGram (x n) - 1‖) cofinite
      (nhds 0) := by
    simpa only [StableFinitenessSentencesCore.cornerGram_eq_star_mul_self]
      using hgram
  exact ⟨StableFinitenessSentencesCore.polarPatch_tendsto_sub x hgram',
    StableFinitenessSentencesCore.polarPatchSeq_mk_eq hx hgram'⟩

/-- **Proof sentence `b21cf7f0f627`.**  "So `vv^*=1`, and `A` is
finite." -/
theorem sentence_b21cf7f0f627 (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    {v : stableFiniteCorona X} (hv : star v * v = 1) : v * star v = 1 :=
  StableFinitenessSentencesCore.isometry_eq_unitary hv

/-- **Proof sentence `993df6a79c44`.**  "For every `k≥1`, apply this
construction with matrix sizes `km_n` to see that
`∏_nM_{km_n}(ℂ)/⊕_nM_{km_n}(ℂ)` is finite."  This is `sentence_b21cf7f0f627`
(equivalently, `StableFinitenessSentencesCore.isometry_eq_unitary`)
re-applied verbatim at the amplified base family `n ↦ Fin k × X n`, whose
cardinality at stage `n` is `k * m_n`.

The printed hypothesis "`k≥1`" is carried here as `[Nonempty (Fin k)]`
rather than `0 < k`: the two are the same content (`Fin k` is nonempty iff
`1 ≤ k`), and `NormMatrixCStarCorona` needs the instance form to form the
amplified corona's type at all, matching the convention already used for
this exact amplification in `Analysis/MatrixCoronaAmplificationEmbedding.lean`
and `Analysis/CompatibleMatrixCoronaAmplification.lean`. -/
theorem sentence_993df6a79c44 (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (k : ℕ) [Nonempty (Fin k)] :
    ∀ v : NormMatrixCStarCorona (fun n ↦ (Fin k × X n : Type)),
      star v * v = 1 → v * star v = 1 :=
  fun v hv ↦ StableFinitenessSentencesCore.isometry_eq_unitary hv

/-- **Proof sentence `36cd63cf2803`, first clause (assumed).**  "This corona
is canonically isomorphic to `M_k(A)`."

This exact isomorphism -- `CStarMatrix I I (NormMatrixCStarCorona X) ≃⋆
NormMatrixCStarCorona (I × X)` -- is independently documented as a genuine,
unbuilt analytic gap in two places already on `origin/main`:
`Analysis/MFStablyFinite.lean` ("`M_I(Q_X)` is again a norm-matrix corona ...
That is not a formality in Lean ... Neither is in Mathlib and neither is in
this repository") and `Analysis/MatrixCoronaDedekindFinite.lean` ("this file
does not construct `M_I(ℓ∞)/M_I(c₀) ≃ ℓ∞/c₀` at all ... building it is not
the cheapest route").  This declaration states the isomorphism the printed
sentence asserts, literally, rather than avoid it; see
`sentence_36cd63cf2803_stablyFinite` immediately below for the sentence's
actual consequence, which does not need it. -/
-- TODO(open): construct the canonical star-algebra isomorphism between
-- `CStarMatrix (Fin k) (Fin k) A` and the norm-matrix corona of amplified
-- matrix sizes `km_n`.  Needs (i) the `CStarMatrix` norm over an `ℓ∞`
-- product identified with the supremum of the coordinate matrix norms, and
-- (ii) `M_{Fin k}` of the `c₀` ideal identified with the `c₀` ideal of the
-- amplified sequence; neither is in the pinned Mathlib or this repository
-- (see the module docstrings cited above).
def MatrixAmplificationCoronaIsomorphism : Prop :=
  ∀ (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (k : ℕ) [Nonempty (Fin k)],
    Nonempty (CStarMatrix (Fin k) (Fin k) (stableFiniteCorona X) ≃⋆ₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ (Fin k × X n : Type)))

/-- **Proof sentence `36cd63cf2803`, second clause.**  "so `A` is stably
finite."  Proved directly, by the abstract Neumann-series route of
`Analysis/MatrixCoronaDedekindFinite.lean`
(`MatrixCoronaFinite.mul_eq_one_symm_matrixCorona`) -- the same route
`Manuscript/OneSidedMFRadical/StableFiniteness.lean` itself uses for this
conjunct -- so that this printed consequence is established unconditionally,
independently of the assumed `MatrixAmplificationCoronaIsomorphism`. -/
theorem sentence_36cd63cf2803_stablyFinite (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (k : ℕ) (hk : 0 < k) :
    ∀ v : Matrix (Fin k) (Fin k) (stableFiniteCorona X),
      star v * v = 1 → v * star v = 1 :=
  fun v hv ↦ MatrixCoronaFinite.mul_eq_one_symm_matrixCorona ⟨⟨0, hk⟩⟩ X hv

/-- **Proof sentence `9b9e5b396d6f`.**  "Finally, let `p≤q` be equivalent
projections in a stably finite algebra `B`, and choose a partial isometry
`w` with `w^*w=q` and `ww^*=p`." -/
theorem sentence_9b9e5b396d6f {B : Type*} [CStarAlgebra B]
    (_hfinite : ∀ x : B, star x * x = 1 → x * star x = 1) {p q : B}
    (_hp : IsStarProjection p) (_hq : IsStarProjection q) (_hle : q * p = p)
    (hequiv : MurrayVonNeumannEquiv p q) :
    ∃ w : B, star w * w = q ∧ w * star w = p :=
  hequiv.symm

/-- **Proof sentence `70c4de929477`.**  "Then `w∈qBq` is an isometry in the
finite corner `qBq`, so `p=ww^*=q`." -/
theorem sentence_70c4de929477 {B : Type*} [CStarAlgebra B]
    (hfinite : ∀ x : B, star x * x = 1 → x * star x = 1) {p q : B}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hle : q * p = p)
    {w : B} (hw1 : star w * w = q) (hw2 : w * star w = p) : p = q := by
  have hequiv : MurrayVonNeumannEquiv p q :=
    MurrayVonNeumannEquiv.symm ⟨w, hw1, hw2⟩
  exact cstar_eq_of_murrayVonNeumannEquiv_of_absorbs hfinite hp hq hle hequiv

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
