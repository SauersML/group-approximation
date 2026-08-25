import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerProjectionZeroAssembly
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanSentenceAudit
import GroupApproximation.Manuscript.OneSidedMFRadical.ShadowResidual

/-!
# The corrected-corner Kazhdan projection, and the printed sentence it feeds

`non_mf_groups_exist.tex`, the outline paragraph of `\begin{mainthm}` and the
printed proof of `\begin{theorem}[normal Kazhdan radical theorem]`:

> A Kazhdan inequality gives an element of `K` whose Hilbert--Schmidt distance
> from the identity is bounded below there, contrary to the first conclusion.

The per-sentence census grades that sentence `partial`, because the three
printed steps existed only separately: `printed_corner_trace_inequality` took
the coordinate quadratic-form inequality as a hypothesis, and every
corrected-corner declaration carried `CorrectedCornerKazhdanProjectionZero`
as a *leading* binder, which is what kept all of them out of the
`#audit_closed_axioms` roster.

## What is proved here

`CorrectedCornerProjectionZeroAssembly` discharges that leading hypothesis for
the constructed corner: `exists_correctedCornerKazhdanProjectionZero` produces
a `CorrectedCornerProvenanceData` for which
`CorrectedCornerKazhdanProjectionZero` *holds*, at every ultrafilter refining
`cofinite`, from the unchanged ambient manuscript hypotheses.  What this module
adds is the printed sentence itself, as named closed propositions whose
quantifiers and hypotheses all live *inside* the statement -- the shape
`#audit_closed_axioms` accepts, since the macro throws on any leading binder.

* `PrintedCorrectedCornerKazhdanProjectionZero` -- printed sentence 177 ("In
  the corner `q𝒬q`, the Kazhdan projection is zero") on the *actual*
  polar-corrected corner, not on an abstract idempotent.
  `manuscriptSentence177_cornerKazhdanProjectionZero` is the abstract identity
  `(1-p)p(1-p) = 0`; this is the statement that the relabelled corrected-corner
  representation really is compression by `q = 1 - p`, so that the maximal
  Kazhdan projection maps to zero in it.
* `PrintedCorrectedCornerKazhdanDetection` -- the printed sentence above.  From
  a corona representation that is nontrivial on `K`, the Kazhdan inequality
  produces one fixed element `k₀` of `K` (in the Kazhdan set) whose normalized
  Hilbert--Schmidt distance from the corner identity stays above the printed
  positive constant `κ²/(2|S|)` along a literal subsequence, and which
  therefore does **not** lie in `R_{∞→2}(G)`.  The last clause is the printed
  "contrary to the first conclusion", stated positively.
* `PrintedNormalKazhdanCoronaTriviality` -- the contradiction discharged: with
  the printed hypothesis `K ≤ R_{∞→2}(G)` in force, every corona
  representation of `G` is trivial on `K`.
* `PrintedNormalKazhdanCornerParagraph` -- the three as one closed
  proposition.

The escape clause is the join of two facts that were separately available:
`P.corner.cornerRepresentation` is an `OpAlmostRepresentation G` whose model
and map are `cornerModel` and `cornerMap` definitionally, and
`mem_opToHSShadowResidual_iff_forall_hsKernel` says that membership in
`R_{∞→2}(G)` forces that displacement to vanish along `atTop`.  Restriction to
the property-`(T)` subgroup costs nothing here: `P.subgroupCorner K` is
`P.corner` precomposed with `K.subtype`, so its corner models and corrected
maps are the ambient ones evaluated at `(k₀ : G)`, definitionally, which is
why the detected element is an element of the *ambient* group and the residual
that it escapes is the ambient `R_{∞→2}(G)`.

## What is not claimed

Nothing here touches `Rad_MF`.  `thm:normal-kazhdan` prints
`K ≤ Rad_{MF}(G)`, and the step from "every corona representation kills `K`"
to that containment is unchanged and remains the business of
`CoronaImageNormalKazhdan`; `PrintedNormalKazhdanCoronaTriviality` stops at
the corona conclusion, which is exactly what the printed proof's final
contradiction establishes.

Nor is any *new* endpoint claimed.  `NormalKazhdanRadical` is already closed,
under the same hypotheses and with the stronger conclusion
`K ≤ Rad_{MF}(G)`, by `normalKazhdan_le_normMFResidual_of_le_opToHSShadowResidual`
along the moving-corner route.  What is new here is only the *route*: the
printed corrected-corner argument now reaches the printed contradiction with
no projection-zero premise, which is what the `partial` census row recorded as
missing.

Nor is the *ambient* group given property `(T)`: the Kazhdan datum belongs to
`K`, as printed, and the corner is restricted along `K.subtype` before the
Kazhdan argument is applied.

## Non-vacuity

The hypotheses of all three propositions are satisfiable, and are *not* the
hypotheses of a reductio.  `PrintedCorrectedCornerKazhdanProjectionZero` and
`PrintedCorrectedCornerKazhdanDetection` ask for a countable `G`, a normal
property-`(T)` subgroup `K`, and a corona representation of `G` that is
nontrivial on `K` -- and they do **not** ask for `K ≤ R_{∞→2}(G)`, so a finite
group -- which has property `(T)` by `hasKazhdanPropertyT_of_finite`, the
manuscript's own sentence, and a corona representation separated from `1` by a
constant unitary sequence -- satisfies them.  It is only the extra printed
hypothesis `K ≤ R_{∞→2}(G)` of `PrintedNormalKazhdanCoronaTriviality` that is
incompatible with a surviving corona image, which is the printed
contradiction; that proposition is stated in positive form (`Θ(k) = 1`) rather
than as an implication into `False`, so it says which conclusion the
contradiction establishes.

`CorrectedCornerProvenanceData` itself is inhabited under exactly those
hypotheses by `exists_correctedCornerProvenanceData`, and `KazhdanData` by
`exists_kazhdanData`, so no existential below is empty for a bad reason.

## Manuscript status

Closes the `partial` census row for the outline sentence of `\begin{mainthm}`
and the corresponding sentences of the printed proof of
`thm:normal-kazhdan`, by removing the projection-zero premise from the printed
corner route.  The endpoint of `thm:normal-kazhdan` is unchanged.

No theorem from the literature is an input.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix PrintedCornerCompression
open MaximalCStarKazhdanProjection

noncomputable section

variable {G : Type} [Group G] [Countable G]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-! ## The detected element, at the ambient corner and outside the residual -/

/-- **The printed detection sentence for one provenance-rich corner.**  Given
the corrected-corner projection-zero identification at `ω`, the Kazhdan
inequality produces a fixed element `k₀` of the Kazhdan set of `K` such that

* the printed constant `κ²/(2|S|)` is strictly positive;
* the normalized Hilbert--Schmidt distance of the *ambient* corrected corner
  map `W_{ψ n}(k₀)` from the corner identity stays above it along a literal
  subsequence `ψ`;
* consequently `k₀` does not lie in the shadow residual `R_{∞→2}(G)`.

The second clause is stated at `P.corner`, the ambient corner, rather than at
its restriction `P.subgroupCorner K`: the two have the same corner models and
the same corrected maps by construction, and only the ambient reading meets
`opToHSShadowResidual G`, whose defining quantifier runs over operator-norm
asymptotic representations of `G`. -/
theorem correctedCornerProvenance_printedDetection
    (K : Subgroup G) (P : CorrectedCornerProvenanceData G X K)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (hzero : CorrectedCornerKazhdanProjectionZero (P.subgroupCorner K) ω hω
      P.kazhdan) :
    ∃ k0 : K, k0 ∈ P.kazhdan.S ∧
      0 < P.kazhdan.kappa ^ 2 / (2 * P.kazhdan.S.card) ∧
      (∃ psi : ℕ → ℕ, StrictMono psi ∧ ∀ n,
        P.kazhdan.kappa ^ 2 / (2 * P.kazhdan.S.card) ≤
          hsNormSq (P.corner.cornerModel (psi n))
            ((P.corner.cornerMap (psi n) (k0 : G) :
              Matrix (P.corner.cornerModel (psi n))
                (P.corner.cornerModel (psi n)) ℂ) - 1)) ∧
      (k0 : G) ∉ opToHSShadowResidual G := by
  obtain ⟨k0, hk0, psi, hpsi, hbound⟩ :=
    manuscriptSentence156_correctedCornerKazhdanDetection
      (P.subgroupCorner K) ω hω P.kazhdan hzero
  have hpos : 0 < P.kazhdan.kappa ^ 2 / (2 * P.kazhdan.S.card) := (hbound 0).1
  have hambient : ∀ n,
      P.kazhdan.kappa ^ 2 / (2 * P.kazhdan.S.card) ≤
        hsNormSq (P.corner.cornerModel (psi n))
          ((P.corner.cornerMap (psi n) (k0 : G) :
            Matrix (P.corner.cornerModel (psi n))
              (P.corner.cornerModel (psi n)) ℂ) - 1) :=
    fun n ↦ (hbound n).2
  refine ⟨k0, hk0, hpos, ⟨psi, hpsi, hambient⟩, ?_⟩
  intro hmem
  have hker : (k0 : G) ∈ hsKernel P.corner.cornerRepresentation :=
    (mem_opToHSShadowResidual_iff_forall_hsKernel (k0 : G)).mp hmem
      P.corner.cornerRepresentation
  have hnull : IsHSNull P.corner.cornerRepresentation (k0 : G) := hker
  obtain ⟨N, hN⟩ := hnull _ hpos
  have hsmall : hsNormSq (P.corner.cornerModel (psi N))
      ((P.corner.cornerMap (psi N) (k0 : G) :
        Matrix (P.corner.cornerModel (psi N))
          (P.corner.cornerModel (psi N)) ℂ) - 1)
      < P.kazhdan.kappa ^ 2 / (2 * P.kazhdan.S.card) :=
    hN (psi N) hpsi.le_apply
  exact absurd hsmall (not_lt.mpr (hambient N))

/-! ## Printed sentence 177 on the actual polar-corrected corner -/

/-- **"In the corner `q𝒬q`, the Kazhdan projection is zero."**  The concrete
form of the printed sentence, on the corner the manuscript actually builds:
from a countable `G`, a normal property-`(T)` subgroup `K`, and a corona
representation of `G` that survives on `K`, there is a provenance-rich
corrected corner in which the maximal Kazhdan projection of `C*_max(K)` maps
to zero, at every ultrafilter refining `cofinite`.

`manuscriptSentence177_cornerKazhdanProjectionZero` is the abstract algebraic
identity `(1-p)p(1-p) = 0` for an idempotent in a ring.  What is stated here
is the datum that identity is *about*: the relabelled corrected-corner
representation is compression by `q = 1 - p` for `p` the represented Kazhdan
projection, so the projection dies in it. -/
def PrintedCorrectedCornerKazhdanProjectionZero : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (K : Subgroup G) (_hnormal : K.Normal)
    (_hT : HasKazhdanPropertyT.{0, 0} K)
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n))) (k : K),
    ((rho (k : G) : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) ≠ 1 →
      ∃ P : CorrectedCornerProvenanceData G X K,
        ∀ (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite),
          CorrectedCornerKazhdanProjectionZero (P.subgroupCorner K) ω hω
            P.kazhdan

/-- Closed proof of printed sentence 177 on the actual corrected corner. -/
theorem manuscriptPrintedCorrectedCornerKazhdanProjectionZero :
    PrintedCorrectedCornerKazhdanProjectionZero := by
  intro G _ _ X _ K hnormal hT rho k hk
  letI := hnormal
  obtain ⟨KD⟩ := exists_kazhdanData _ hT
  exact exists_correctedCornerKazhdanProjectionZero K rho KD k hk

/-! ## The printed Kazhdan-inequality sentence -/

/-- **"A Kazhdan inequality gives an element of `K` whose Hilbert--Schmidt
distance from the identity is bounded below there, contrary to the first
conclusion."**

From the same hypotheses -- a countable `G`, a normal property-`(T)` subgroup
`K`, and a corona representation surviving on `K` -- there is a corrected
corner such that, at every ultrafilter refining `cofinite`, the Kazhdan
inequality produces one fixed element `k₀ ∈ K` with

* `k₀` in the Kazhdan set of `K`;
* the printed constant `κ²/(2|S|)` strictly positive;
* `‖W_{ψ n}(k₀) - q_{ψ n}‖₂² ≥ κ²/(2|S|)` along a literal subsequence `ψ`,
  which is "bounded below there";
* `k₀ ∉ R_{∞→2}(G)`, which is "contrary to the first conclusion".

The projection-zero premise that every corrected-corner declaration used to
carry has been discharged inside the proof, not assumed. -/
def PrintedCorrectedCornerKazhdanDetection : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (K : Subgroup G) (_hnormal : K.Normal)
    (_hT : HasKazhdanPropertyT.{0, 0} K)
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n))) (k : K),
    ((rho (k : G) : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) ≠ 1 →
      ∃ P : CorrectedCornerProvenanceData G X K,
        ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ cofinite →
          ∃ k0 : K, (k0 : G) ∈ K ∧ k0 ∈ P.kazhdan.S ∧
            0 < P.kazhdan.kappa ^ 2 / (2 * P.kazhdan.S.card) ∧
            (∃ psi : ℕ → ℕ, StrictMono psi ∧ ∀ n,
              P.kazhdan.kappa ^ 2 / (2 * P.kazhdan.S.card) ≤
                hsNormSq (P.corner.cornerModel (psi n))
                  ((P.corner.cornerMap (psi n) (k0 : G) :
                    Matrix (P.corner.cornerModel (psi n))
                      (P.corner.cornerModel (psi n)) ℂ) - 1)) ∧
            (k0 : G) ∉ opToHSShadowResidual G

/-- Closed proof of the printed Kazhdan-inequality sentence. -/
theorem manuscriptPrintedCorrectedCornerKazhdanDetection :
    PrintedCorrectedCornerKazhdanDetection := by
  intro G _ _ X _ K hnormal hT rho k hk
  letI := hnormal
  obtain ⟨KD⟩ := exists_kazhdanData _ hT
  obtain ⟨P, hzero⟩ :=
    exists_correctedCornerKazhdanProjectionZero K rho KD k hk
  refine ⟨P, fun ω hω ↦ ?_⟩
  obtain ⟨k0, hk0, hpos, hsub, hout⟩ :=
    correctedCornerProvenance_printedDetection K P ω hω (hzero ω hω)
  exact ⟨k0, k0.2, hk0, hpos, hsub, hout⟩

/-! ## The printed contradiction, discharged -/

/-- **The printed final contradiction of `thm:normal-kazhdan`, as its positive
conclusion.**  With the printed standing hypothesis `K ≤ R_{∞→2}(G)` in force
-- which is what `K ≤ D ≤ R_{∞→2}(G)` supplies -- no corona representation of
`G` can survive on the normal property-`(T)` subgroup `K`: every one of them
sends every element of `K` to the identity of the corona.

This is the printed proof's own route: a surviving `Θ` builds the
complementary corner, the Kazhdan inequality detects an element of `K` at a
positive Hilbert--Schmidt distance from the corner identity along a
subsequence, and that contradicts invisibility of `K` in the corner
asymptotic representation.  No compression datum, and no property-`(T)`
hypothesis on the ambient group, is used.

What is *not* asserted is the printed containment `K ≤ Rad_{MF}(G)` itself;
the passage from corona triviality to the MF radical is unchanged and lives in
`CoronaImageNormalKazhdan`. -/
def PrintedNormalKazhdanCoronaTriviality : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (K : Subgroup G) (_hnormal : K.Normal),
    HasKazhdanPropertyT.{0, 0} K →
      K ≤ opToHSShadowResidual G →
        ∀ (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n))) (k : K),
          ((rho (k : G) : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) = 1

/-- Closed proof of the printed final contradiction. -/
theorem manuscriptPrintedNormalKazhdanCoronaTriviality :
    PrintedNormalKazhdanCoronaTriviality := by
  intro G _ _ X _ K hnormal hT hresidual rho k
  letI := hnormal
  by_contra hk
  obtain ⟨KD⟩ := exists_kazhdanData _ hT
  obtain ⟨P, hzero⟩ :=
    exists_correctedCornerKazhdanProjectionZero K rho KD k hk
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have hU : ((U : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
    Ultrafilter.of_le _
  obtain ⟨k0, _hk0, _hpos, _hsub, hout⟩ :=
    correctedCornerProvenance_printedDetection K P U hU (hzero U hU)
  exact hout (SetLike.le_def.mp hresidual k0.2)

/-! ## The paragraph -/

/-- The corrected-corner sentences of the printed normal-Kazhdan proof, in
printed order, as one closed proposition. -/
def PrintedNormalKazhdanCornerParagraph : Prop :=
  PrintedCorrectedCornerKazhdanProjectionZero ∧
    PrintedCorrectedCornerKazhdanDetection ∧
    PrintedNormalKazhdanCoronaTriviality

/-- Closed proof of the complete printed paragraph. -/
theorem manuscriptPrintedNormalKazhdanCornerParagraph :
    PrintedNormalKazhdanCornerParagraph :=
  ⟨manuscriptPrintedCorrectedCornerKazhdanProjectionZero,
    manuscriptPrintedCorrectedCornerKazhdanDetection,
    manuscriptPrintedNormalKazhdanCoronaTriviality⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
