import GroupApproximation.Manuscript.OneSidedMFRadical.PartialClosureAnalysis
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanSentenceAudit
import GroupApproximation.Manuscript.OneSidedMFRadical.ShadowResidual
import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerGramSequence
import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaKazhdanOrder

/-!
# Printed sentences whose Lean attachment was only partial, second wave

`PartialClosureAnalysis.lean` closed six rows of the per-sentence audit of
`non_mf_groups_exist.tex`.  Four more became reachable when the universal GNS
representation (`CStarState.universalGNSStarAlgHom_injective`) and the
corrected-corner detection theorems landed.  As in that file, each entry is a
named `Prop` whose quantifiers and hypotheses live *inside* the statement --
the shape `#audit_closed_axioms` accepts -- together with a theorem proving
it.

## What is closed here

* **`lem:kazhdan-projection-order`, "Represent `B` faithfully and
  nondegenerately on a Hilbert space `H`."**
  (`PrintedFaithfulNondegenerateRepresentation`).  Both audited declarations
  took the faithful representation as an *input*
  (`faithfulRep : B →⋆ₐ[ℂ] (E →L[ℂ] E)` together with its injectivity); no
  declaration *produced* one, and
  `Analysis/MaximalCStarKazhdanProjection.lean` says so explicitly under
  *Not claimed*.  The statement below produces it: for every nontrivial unital
  complex C-star algebra there **exist** a complete complex inner-product
  space and a faithful unital `⋆`-homomorphism into its bounded operators.
  Nondegeneracy is included, in the form it takes for a unital
  representation: `π(1) = 1`, hence every vector is `π(b)η` for some `b, η`,
  so `π(B)H = H` and a fortiori is dense.

* **`lem:central-corona-corner` / `thm:normal-kazhdan`, "The coordinate
  elements `b_n = |S|⁻¹ ∑_s (W_n(s) - q_n)^*(W_n(s) - q_n)` represent `b`."**
  (`PrintedCoordinateGramRepresents`).  See *What is weaker* below: what is
  proved is that the corona class of the coordinate sequence is the Gram
  element formed from the corona classes of the `W_n(s)`.

* **`thm:normal-kazhdan`, "This contradicts `s₀ ∈ K ≤ D ≤ R_{∞→2}(G)`."**
  (`PrintedCornerFinalContradiction`).  The two halves existed separately --
  `manuscriptSentence156_correctedCornerKazhdanDetection` produces the fixed
  `s₀ ∈ S` with a uniform positive normalized Hilbert--Schmidt displacement
  along a subsequence, and `mem_opToHSShadowResidual_iff_forall_hsKernel` says
  membership in `R_{∞→2}(G)` makes that displacement vanish -- but no module
  mentioned both `cornerRepresentation` and `opToHSShadowResidual`, so the
  printed contradiction was not a statement anywhere.  The joint is the
  observation that `D.cornerRepresentation` *is* an `OpAlmostRepresentation`
  whose model and map are `D.cornerModel` and `D.cornerMap` definitionally, so
  `K₂(D.cornerRepresentation)` is a condition on exactly the quantity the
  detection theorem bounds from below.

* **`lem:stable-finite`, "For all sufficiently large `n`, the matrix `x_n` is
  invertible, and the unitary `x_n(x_n^*x_n)^{-1/2}` differs from `x_n` by
  `o(1)`."**  (`PrintedEventualInvertibilityAndPolarDistance`).
  `manuscriptPrintedOneSidedPolarCorrection` is the statement at one block,
  under the quantitative hypothesis `‖x^*x - 1‖ ≤ 1/2`.  The printed sentence
  is the *eventual* statement about a sequence, under the printed hypothesis
  `x_n^*x_n → 1`, and that is what is stated here: "for all sufficiently
  large `n`" is `∀ᶠ n in cofinite`, and the printed `o(1)` is
  `Tendsto … cofinite (𝓝 0)`.  The block-level instance is the one
  `PartialClosureAnalysis` already elaborated, re-enabled here with
  `attribute [local instance]` so that the two statements speak of the same
  `polarUnitary`.

## What is weaker, and exactly how

`PrintedCoordinateGramRepresents` says

    `mk (b_n)_n = ∑_{s∈S} (mk (W_·(s)) - 1)^* (mk (W_·(s)) - 1)`

in the corner corona: the class of the coordinate sequence is the printed
Gram expression, formed from the corona classes of the corrected corner maps
`W_n(s)`.  (`unitaryGram` is the unnormalized `|S|·b`, and the unit of the
corner algebra is the printed `q`; the printed `q_n` is the unit of the
`n`-th corner block, which is why `1` appears where the manuscript writes
`q_n`.)  The manuscript defines `b` two displays earlier through `Θ`, as
`|S|⁻¹ ∑_s (qΘ(s)q - q)^*(qΘ(s)q - q)`, so carrying the printed sentence in
full needs in addition

    `mk (W_·(s)) = q Θ(s) q`

in the *corner* corona.  That identification is not proved below and is not in
the tree: `manuscriptCentralCoronaCorner`'s class equation lives in the
*ambient* corona (`normMatrixCStarCoronaMk (Q·U·Q) = q·ρ(g)`), and moving it
to the corner corona is the corner-corona embedding, which is exactly the
hypothesis `hclass` of `manuscriptPrintedCornerCoronaKazhdanOrder`.  So the
"represent" step is closed at the level of the classes of the `W_n(s)` and
open at the level of `Θ`.

## Non-vacuity

`PrintedFaithfulNondegenerateRepresentation` and
`PrintedEventualInvertibilityAndPolarDistance` are universally quantified
implications whose hypotheses are satisfied by, respectively, every nontrivial
unital C-star algebra in the development (the corner corona, by
`OmegaCoronaKazhdanProjection.coronaNontrivial`) and by every bounded lift of
a corona isometry.  `PrintedCoordinateGramRepresents` is an unconditional
identity.

`PrintedCornerFinalContradiction` is a *refutation*: its content is that the
listed hypotheses cannot all hold, which is what "This contradicts …" asserts.
Its first conclusion is stated positively -- some element of the Kazhdan set
is **not** in `R_{∞→2}(G)` -- so that the declaration says which conclusion
the printed contradiction establishes and is not merely an implication into
`False`.  Each hypothesis is separately satisfiable: `PrintedCornerData` is
produced by `manuscriptCentralCoronaCorner`, `KazhdanData` by
`exists_kazhdanData`, and `CorrectedCornerKazhdanProjectionZero` by
`CorrectedCornerProjectionZeroAssembly`.

## Manuscript status

Certifies three previously partial printed clauses and weakens a fourth in the
one respect recorded above.  No endpoint changes.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter
open PrintedCornerCompression
open scoped Matrix.Norms.L2Operator

attribute [local instance] matrixBlockCStarAlgebra

noncomputable section

/-! ## `lem:kazhdan-projection-order`: producing the faithful representation

`non_mf_groups_exist.tex`:

> Represent `B` faithfully and nondegenerately on a Hilbert space `ℋ`.

Both declarations previously attached to this sentence consumed a faithful
representation rather than producing one, and the header of
`Analysis/MaximalCStarKazhdanProjection.lean` records under *Not claimed* that
nothing in the tree asserted `B` has one.  `CStarState.universalGNSStarAlgHom`
and its injectivity now supply the construction: the Hilbert `ℓ²`-sum of the
GNS spaces of all states, with `B` acting diagonally. -/

section FaithfulRepresentation

/-- **"Represent `B` faithfully and nondegenerately on a Hilbert space `ℋ`."**
For every nontrivial unital complex C-star algebra `B` there are a complex
inner-product space `E`, complete for its norm, and a `⋆`-algebra
homomorphism `π : B → 𝔅(E)` which is

* **faithful**: `π` is injective;
* **unital**: `π 1 = 1`;
* **nondegenerate**: every vector of `E` is of the form `π(b)η`, so the
  action of `B` on `E` has no degenerate part -- `π(B)E = E`, hence a fortiori
  `π(B)E` is dense.

Nondegeneracy is included rather than left open: for a *unital*
representation of a unital algebra it is a consequence of `π 1 = 1`, which is
the manuscript's situation (`B` is a unital corner corona and the printed
representation is unital).  What the statement does *not* assert is that an
arbitrary, possibly non-unital, representation can be cut down to a
nondegenerate one.

Nontriviality of `B` is a hypothesis because the universal GNS space is built
from the states of `B`, and a trivial algebra has none. -/
def PrintedFaithfulNondegenerateRepresentation : Prop :=
  ∀ (B : Type) [CStarAlgebra B] [Nontrivial B],
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E)
      (_ : CompleteSpace E) (pi : B →⋆ₐ[ℂ] (E →L[ℂ] E)),
        Function.Injective pi ∧ pi 1 = 1 ∧
          ∀ xi : E, ∃ (b : B) (eta : E), pi b eta = xi

/-- Closed proof that every nontrivial unital complex C-star algebra has a
faithful nondegenerate Hilbert-space representation. -/
theorem manuscriptPrintedFaithfulNondegenerateRepresentation :
    PrintedFaithfulNondegenerateRepresentation := by
  intro B _ _
  refine ⟨CStarState.UniversalGNSSpace B, inferInstance, inferInstance,
    inferInstance, CStarState.universalGNSStarAlgHom,
    CStarState.universalGNSStarAlgHom_injective,
    map_one (CStarState.universalGNSStarAlgHom (A := B)), ?_⟩
  intro xi
  refine ⟨1, xi, ?_⟩
  calc (CStarState.universalGNSStarAlgHom (A := B)) 1 xi
      = (1 : CStarState.UniversalGNSSpace B →L[ℂ]
          CStarState.UniversalGNSSpace B) xi := by
        rw [map_one (CStarState.universalGNSStarAlgHom (A := B))]
    _ = xi := rfl

end FaithfulRepresentation

/-! ## `thm:normal-kazhdan`: the coordinate elements represent `b`

`non_mf_groups_exist.tex`:

> The coordinate elements `b_n = |S|⁻¹ ∑_{s∈S}(W_n(s) - q_n)^*(W_n(s) - q_n)`
> represent `b`.

`correctedCornerSectorGramSequence D S` is the printed `(b_n)` as one element
of the bounded-sequence algebra, and `correctedCornerSectorGramSequence_apply`
identifies its coordinates.  What was missing is the passage of that sequence
through the corona quotient, which is what "represent" means. -/

section RepresentingGram

/-- **"The coordinate elements `b_n` represent `b`."**  The corona class of
the printed coordinate sequence `(b_n)` is the printed Gram element built from
the corona classes of the corrected corner maps `W_n(s)`.

`unitaryGram S U = ∑_{s∈S} (U s - 1)^*(U s - 1)` is the unnormalized `|S|·b`,
and `1` stands where the manuscript writes `q_n`, because `q_n` is the unit of
the `n`-th corner block and `q` the unit of the corner corona.

**This is weaker than the printed sentence in one named respect.**  The
manuscript's `b` is written through `Θ`, as
`|S|⁻¹ ∑_s (qΘ(s)q - q)^*(qΘ(s)q - q)`.  The statement below produces the
Gram element over the corona classes of the `W_n(s)`; the further
identification of those classes with `qΘ(s)q` in the *corner* corona is not
proved here and is not in the tree -- it is the `hclass` hypothesis of
`manuscriptPrintedCornerCoronaKazhdanOrder`, and it needs the corner-corona
embedding rather than the ambient class equation of
`manuscriptCentralCoronaCorner`.

The identity holds at every filter, `cofinite` and a free ultrafilter alike;
no hypothesis on the corner data is used, because it is the statement that the
quotient map is a `⋆`-homomorphism, applied to the printed expression. -/
def PrintedCoordinateGramRepresents : Prop :=
  ∀ (G : Type) [Group G] (model : ℕ → FiniteModel)
    (D : PrintedCornerData G model) (S : Finset G) (l : Filter ℕ),
      filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l
          (correctedCornerSectorGramSequence D S)
        = unitaryGram S fun s ↦
            filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l
              (correctedCornerMapSequence D s)

/-- Closed proof that the printed coordinate elements represent the printed
Gram element of the corner corona. -/
theorem manuscriptPrintedCoordinateGramRepresents :
    PrintedCoordinateGramRepresents := by
  intro G _ model D S l
  simp only [correctedCornerSectorGramSequence, unitaryGram]
  rw [map_sum (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l)]
  refine Finset.sum_congr rfl fun s _hs ↦ ?_
  have hsub : filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l
        (correctedCornerMapSequence D s - 1)
      = filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l
          (correctedCornerMapSequence D s) - 1 := by
    rw [map_sub (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l),
      map_one (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l)]
  have hstar : filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l
        (star (correctedCornerMapSequence D s - 1))
      = star (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l
          (correctedCornerMapSequence D s - 1)) :=
    (filterMatrixCStarCorona_star_mk (fun n ↦ D.cornerModel n) l
      (correctedCornerMapSequence D s - 1)).symm
  rw [map_mul (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) l),
    hstar, hsub]

end RepresentingGram

/-! ## `thm:normal-kazhdan`: the printed final contradiction

`non_mf_groups_exist.tex`:

> After passing to a subsequence, one fixed `s₀ ∈ S` therefore stays a
> positive Hilbert--Schmidt distance from the corner identity.  This
> contradicts `s₀ ∈ K ≤ D ≤ R_{∞→2}(G)`.

The two halves were separately available and were never joined. -/

section FinalContradiction

/-- **"This contradicts `s₀ ∈ K ≤ D ≤ R_{∞→2}(G)`."**

From the corrected-corner projection-zero interface, the printed subsequence
argument produces a fixed `s₀` of the Kazhdan set whose normalized
Hilbert--Schmidt displacement from the corner identity stays above
`κ²/(2|S|) > 0` along a strictly increasing sequence of coordinates.  The
corner representation is an `OpAlmostRepresentation`, so membership of `s₀` in
the shadow residual `R_{∞→2}(G)` would force that displacement to tend to `0`.
Hence:

* some element of the Kazhdan set is **not** in `R_{∞→2}(G)`;
* the printed chain `s₀ ∈ K ≤ D ≤ R_{∞→2}(G)`, read as "every element of the
  Kazhdan set lies in the residual", is contradictory.

The first conclusion is the informative form and the second is the printed
"this contradicts".  The printed chain enters only through its consequence
`S ⊆ R_{∞→2}(G)`: `S ⊆ K` is the choice of a Kazhdan set inside `K`, and
`K ≤ D ≤ R_{∞→2}(G)` is the standing hypothesis of `thm:normal-kazhdan`. -/
def PrintedCornerFinalContradiction : Prop :=
  ∀ (G : Type) [Group G] (model : ℕ → FiniteModel)
    (D : PrintedCornerData G model) (omega : Ultrafilter ℕ)
    (homega : (omega : Filter ℕ) ≤ cofinite) (K : KazhdanData G),
    CorrectedCornerKazhdanProjectionZero D omega homega K →
      (∃ s0 ∈ K.S, s0 ∉ opToHSShadowResidual G) ∧
        ((∀ s ∈ K.S, s ∈ opToHSShadowResidual G) → False)

/-- Closed proof of the printed final contradiction of `thm:normal-kazhdan`. -/
theorem manuscriptPrintedCornerFinalContradiction :
    PrintedCornerFinalContradiction := by
  intro G _ model D omega homega K hzero
  obtain ⟨s0, hs0, phi, hphi, hbound⟩ :=
    manuscriptSentence156_correctedCornerKazhdanDetection D omega homega K hzero
  have houtside : s0 ∉ opToHSShadowResidual G := by
    intro hmem
    have hker : s0 ∈ hsKernel D.cornerRepresentation :=
      (mem_opToHSShadowResidual_iff_forall_hsKernel s0).mp hmem
        D.cornerRepresentation
    have hnull : IsHSNull D.cornerRepresentation s0 := hker
    have hpos : 0 < K.kappa ^ 2 / (2 * K.S.card) := (hbound 0).1
    obtain ⟨N, hN⟩ := hnull _ hpos
    have hsmall := hN (phi N) hphi.le_apply
    have hsmall' : hsNormSq (D.cornerModel (phi N))
        ((D.cornerMap (phi N) s0 :
          Matrix (D.cornerModel (phi N)) (D.cornerModel (phi N)) ℂ) - 1)
        < K.kappa ^ 2 / (2 * K.S.card) := hsmall
    exact absurd hsmall' (not_lt.mpr (hbound N).2)
  exact ⟨⟨s0, hs0, houtside⟩, fun hall ↦ houtside (hall s0 hs0)⟩

end FinalContradiction

/-! ## `lem:stable-finite`: the printed eventual statement

`non_mf_groups_exist.tex`:

> Suppose that `v^*v = 1` in the corona, and let `(x_n)` be a bounded lift of
> `v`.  Then `x_n^*x_n → 1` in norm.  For all sufficiently large `n`, the
> matrix `x_n` is invertible, and the unitary `x_n(x_n^*x_n)^{-1/2}` differs
> from `x_n` by `o(1)`.

`manuscriptPrintedOneSidedPolarCorrection` is this at one block, under
`‖x^*x - 1‖ ≤ 1/2`.  The printed sentence quantifies over a sequence and is
eventual, which is what is stated here. -/

section EventualPolar

/-- **"For all sufficiently large `n`, the matrix `x_n` is invertible, and the
unitary `x_n(x_n^*x_n)^{-1/2}` differs from `x_n` by `o(1)`."**  From the
printed one-sided hypothesis `‖x_n^*x_n - 1‖ → 0`, which is what `v^*v = 1`
gives on a lift:

* `x_n` is invertible for all sufficiently large `n`;
* the printed correction `u_n = x_n(x_n^*x_n)^{-1/2}` is unitary there;
* `‖u_n - x_n‖ → 0`, the printed `o(1)`.

"For all sufficiently large `n`" is `∀ᶠ n in cofinite`, which on `ℕ` is
"outside a finite set" and hence "from some stage on".  The two Gram defects
of `Analysis/PolarLiftingGeneralCStar.printedUnitaryLifting` are not both
assumed: only `x_n^*x_n → 1`, as printed, the second being unavailable at this
point of `lem:stable-finite`. -/
def PrintedEventualInvertibilityAndPolarDistance : Prop :=
  ∀ (Z : ℕ → Type) [∀ n, Fintype (Z n)] [∀ n, DecidableEq (Z n)]
      [∀ n, Nonempty (Z n)] (x : ∀ n, Matrix (Z n) (Z n) ℂ),
      Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) cofinite (nhds 0) →
        (∀ᶠ n in cofinite, IsUnit (x n)) ∧
          (∀ᶠ n in cofinite, PolarLiftingGeneralCStar.polarUnitary (x n) ∈
            unitary (Matrix (Z n) (Z n) ℂ)) ∧
          Tendsto (fun n ↦
              ‖PolarLiftingGeneralCStar.polarUnitary (x n) - x n‖)
            cofinite (nhds 0)

/-- Closed proof of the printed eventual invertibility and polar distance. -/
theorem manuscriptPrintedEventualInvertibilityAndPolarDistance :
    PrintedEventualInvertibilityAndPolarDistance := by
  intro Z _ _ _ x hx
  have hgood : ∀ᶠ n in cofinite, ‖star (x n) * x n - 1‖ ≤ 1 / 2 := by
    have hd := (Metric.tendsto_nhds.mp hx) ((1 : ℝ) / 2) (by norm_num)
    filter_upwards [hd] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hgood] with n hn
    exact (manuscriptPrintedOneSidedPolarCorrection (Z n) (x n) hn).1
  · filter_upwards [hgood] with n hn
    exact (manuscriptPrintedOneSidedPolarCorrection (Z n) (x n) hn).2.1
  · refine squeeze_zero' (g := fun n ↦ 4 * ‖star (x n) * x n - 1‖)
      (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ ?_
    · filter_upwards [hgood] with n hn
      have hxn : ‖x n‖ ≤ 2 := FiniteBlockCorona.norm_le_two_of_gram_le hn
      have hd : ‖PolarLiftingGeneralCStar.polarUnitary (x n) - x n‖
          ≤ 2 * ‖x n‖ * ‖star (x n) * x n - 1‖ :=
        (manuscriptPrintedOneSidedPolarCorrection (Z n) (x n) hn).2.2
      have hprod : 0 ≤ (2 - ‖x n‖) * ‖star (x n) * x n - 1‖ :=
        mul_nonneg (by linarith) (norm_nonneg _)
      nlinarith [hd]
    · simpa using hx.const_mul (4 : ℝ)

end EventualPolar

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
