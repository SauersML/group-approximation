import GroupApproximation.Manuscript.OneSidedMFRadical.CornerClassIdentification
import GroupApproximation.Manuscript.OneSidedMFRadical.PartialClosureAnalysisTwo
import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerKazhdanQuadraticBridge

/-!
# The printed `b`, and `hclass` discharged

`non_mf_groups_exist.tex`, printed proof of `thm:normal-kazhdan`, defines

    `b = |S|⁻¹ ∑_{s∈S} (q Θ(s) q - q)^* (q Θ(s) q - q)`

and then asserts

> The coordinate elements `b_n = |S|⁻¹ ∑_{s∈S} (W_n(s) - q_n)^*(W_n(s) - q_n)`
> represent `b`.

`Manuscript/OneSidedMFRadical/PartialClosureAnalysisTwo.lean` proves that
sentence with `b` written through the corona classes `[W_·(s)]`;
`Manuscript/OneSidedMFRadical/CornerClassIdentification.lean` identifies those
classes with the printed `q Θ(s) q`.  This file composes the two, so that the
printed sentence holds with `b` written the way the manuscript writes it, and
then removes the corresponding hypothesis `hclass` from the printed
corner-corona Kazhdan order.

## What is proved

* `correctedCornerCoronaEmbedHom_printedGram` and
  `PrintedCoordinateGramRepresentsPrintedB` — the printed sentence with `b`
  built from `q Θ(s) q` and `q`, in the ambient corona over the retained
  coordinates.  As everywhere in this development the normalising `|S|⁻¹` is
  carried by the consumer rather than by the Gram element (the convention of
  `sectorGram` and `unitaryGram`), so the displayed element is `|S| · b`.
* `correctedCornerCoronaRepresentation` — the printed `Θ` on the corner: its
  value at `g` is by definition the class of the printed `(W_n(g))`, and its
  ambient reading is `q Θ(g) q` by
  `manuscriptCornerCoronaClassIdentification`.
* `correctedCornerSectorGramSequence_class` — the hypothesis `hclass` of
  `exists_coordinateNormBound_of_cornerCoronaKazhdan`, proved rather than
  assumed.
* `exists_coordinateNormBound_of_correctedCornerKazhdan` — that theorem with
  `hclass` discharged, and
  `exists_coordinateNormBound_of_correctedCornerProjectionZero` — the same with
  the remaining antecedent in its printed projection form.

## What is not claimed

The fixed-vector antecedent `hno` is not derived here.  It remains an
antecedent, in the two equivalent shapes the repository already carries; the
last statement takes it as `CorrectedCornerKazhdanProjectionZero`, which is the
printed sentence that precedes it and is exactly the residue named in the
*What is not claimed* section of `CornerCoronaKazhdanOrder.lean`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open PrintedCornerCompression
open OmegaCoronaKazhdanProjection VectorOmegaAction
open MaximalCStarKazhdanProjection
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

/-! ## The printed `b`, from the printed `(b_n)` -/

section PrintedGram

variable {G : Type} [Group G] {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- **The printed sentence, with `b` written through `Θ`.**  The corona class
of the printed coordinate sequence `(b_n)`, read in the ambient corona through
the printed identification of the corner, is the printed Gram element

    `∑_{s∈S} (q Θ(s) q - q)^* (q Θ(s) q - q)`,

with `q` the printed projection and `q Θ(s) q` the printed compressed
generator.  `z s` is the ambient `Θ(s)` and `hclass` is the class equation of
Lemma `lem:central-corona-corner`, as delivered by
`manuscriptCornerCoronaClass`.

The corner-corona embedding is *nonunital*: it carries the unit of the corner
corona to `q`, which is exactly why the printed displacements are taken against
`q` and not against `1`. -/
theorem correctedCornerCoronaEmbedHom_printedGram {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (Q : BoundedMatrixSequence (fun n ↦ X n))
    (D : PrintedCornerData G (fun k ↦ X (φ k)))
    (q : NormMatrixCStarCorona (fun n ↦ X n)) (hqid : q * q = q)
    (hQ : normMatrixCStarCoronaMk (fun n ↦ X n) Q = q)
    (hDq : ∀ k, D.q k = (Q : ∀ n, Matrix (X n) (X n) ℂ) (φ k))
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (z : G → NormMatrixCStarCorona (fun n ↦ X n))
    (hclass : ∀ g : G,
      normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ambientCornerSeq D g)
        = coronaRestrict X φ hφ (q * z g))
    (S : Finset G) :
    correctedCornerCoronaEmbedHom D (ω : Filter ℕ)
        (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) (ω : Filter ℕ)
          (correctedCornerSectorGramSequence D S))
      = retainedCoronaToOmega X φ hφ ω hω
          (∑ s ∈ S, star (q * z s * q - q) * (q * z s * q - q)) := by
  have hstep : ∀ s : G,
      correctedCornerCoronaEmbedHom D (ω : Filter ℕ)
          (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) (ω : Filter ℕ)
            (correctedCornerMapSequence D s) - 1)
        = retainedCoronaToOmega X φ hφ ω hω (q * z s * q - q) := by
    intro s
    rw [map_sub, map_sub,
      correctedCornerCoronaEmbedHom_class_eq hφ Q D q hqid hQ hDq ω hω (z s) s
        (hclass s),
      correctedCornerCoronaEmbedHom_one_eq hφ Q D q hQ hDq ω hω]
  rw [manuscriptPrintedCoordinateGramRepresents G (fun k ↦ X (φ k)) D S
      (ω : Filter ℕ), unitaryGram,
    map_sum (correctedCornerCoronaEmbedHom D (ω : Filter ℕ)),
    map_sum (retainedCoronaToOmega X φ hφ ω hω)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_mul, map_star, hstep s, map_mul, map_star]

end PrintedGram

/-- **"The coordinate elements `b_n` represent `b`", with `b` as printed.**

Under the hypotheses of Lemma `lem:central-corona-corner` and for any
ultrafilter refining `cofinite`, the printed corner data `D` exists, the
corner-corona embedding `ι` is an isomorphism of the corner corona onto the
printed corner `q 𝒬 q` (injective, with `ι 1 = q` and range the two-sided-cut
fixed points), and for every finite `S` the class of the printed coordinate
sequence `(b_n)` satisfies

    `ι [ (b_n) ]  =  ∑_{s∈S} (q ρ(s) q - q)^* (q ρ(s) q - q)`

in the ambient corona over the retained coordinates.  The right-hand side is
the manuscript's `b` with the normalising `|S|⁻¹` left to the consumer, which
is this development's convention for `sectorGram` and `unitaryGram`.

This is the sentence whose Lean rendering previously stopped at the Gram
element of the corner classes `[W_·(s)]`, with the further identification of
those classes with `q Θ(s) q` recorded as absent. -/
def PrintedCoordinateGramRepresentsPrintedB : Prop :=
  ∀ (G : Type) [Group G] [Countable G]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (q : NormMatrixCStarCorona (fun n ↦ X n)),
    star q = q → q * q = q → q ≠ 0 →
    (∀ g : G, ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) * q =
      q * ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n))) →
    ∀ (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite),
      ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ)
        (D : PrintedCornerData G (fun k ↦ X (φ k))),
        (∀ k, 0 < Fintype.card (D.cornerModel k)) ∧
        (∀ k g, HEq (D.cornerRepresentation.map k g) (D.cornerMap k g)) ∧
        Function.Injective (correctedCornerCoronaEmbedHom D (ω : Filter ℕ)) ∧
        correctedCornerCoronaEmbedHom D (ω : Filter ℕ) 1
          = retainedCoronaToOmega X φ hφ ω hω q ∧
        Set.range (correctedCornerCoronaEmbedHom D (ω : Filter ℕ))
          = {x : FilterMatrixCStarCorona (fun k ↦ X (φ k)) (ω : Filter ℕ) |
              retainedCoronaToOmega X φ hφ ω hω q * x *
                retainedCoronaToOmega X φ hφ ω hω q = x} ∧
        (∀ S : Finset G,
          correctedCornerCoronaEmbedHom D (ω : Filter ℕ)
              (filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n)
                (ω : Filter ℕ) (correctedCornerSectorGramSequence D S))
            = retainedCoronaToOmega X φ hφ ω hω
                (∑ s ∈ S,
                  star (q * ((rho s : unitary
                      (NormMatrixCStarCorona (fun n ↦ X n))) :
                    NormMatrixCStarCorona (fun n ↦ X n)) * q - q) *
                    (q * ((rho s : unitary
                        (NormMatrixCStarCorona (fun n ↦ X n))) :
                      NormMatrixCStarCorona (fun n ↦ X n)) * q - q)))

/-- Closed proof that the printed coordinate elements represent the printed
`b`, with `b` built from the ambient `q Θ(s) q` as the manuscript builds it. -/
theorem manuscriptPrintedCoordinateGramRepresentsPrintedB :
    PrintedCoordinateGramRepresentsPrintedB := by
  intro G _ _ X _ rho q hqstar hqid hqne hcentral ω hω
  obtain ⟨φ, hφ, Q, D, hQproj, hQmk, hDq, hDqne, hcard, hHEq, hclass⟩ :=
    manuscriptCornerCoronaClass G X rho q hqstar hqid hqne hcentral
  exact ⟨φ, hφ, D, hcard, hHEq,
    correctedCornerCoronaEmbedHom_injective D (ω : Filter ℕ),
    correctedCornerCoronaEmbedHom_one_eq hφ Q D q hQmk hDq ω hω,
    correctedCornerCoronaEmbedHom_range hφ Q D q hQmk hDq ω hω,
    fun S ↦ correctedCornerCoronaEmbedHom_printedGram hφ Q D q hqid hQmk hDq
      ω hω _ hclass S⟩

/-! ## `hclass` discharged at its use site -/

section KazhdanOrder

variable {G : Type} [Group G] {model : ℕ → FiniteModel}

/-- **The printed `Θ`, on the corner.**  The corner-corona representation whose
value at `g` is the class of the printed `(W_n(g))`.  Its ambient reading is
`q Θ(g) q` by `manuscriptCornerCoronaClassIdentification`. -/
def correctedCornerCoronaRepresentation (D : PrintedCornerData G model)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    G →* unitary (FilterMatrixCStarCorona
      (fun n ↦ D.cornerModel n) (ω : Filter ℕ)) :=
  coronaRep (fun n ↦ D.cornerModel n) ω
    (correctedCornerOmegaRepresentation D ω hω)

@[simp] theorem correctedCornerCoronaRepresentation_coe
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (g : G) :
    ((correctedCornerCoronaRepresentation D ω hω g : unitary
        (FilterMatrixCStarCorona (fun n ↦ D.cornerModel n) (ω : Filter ℕ))) :
      FilterMatrixCStarCorona (fun n ↦ D.cornerModel n) (ω : Filter ℕ))
      = filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) (ω : Filter ℕ)
          (correctedCornerMapSequence D g) := rfl

/-- **`hclass`, proved.**  The corona class of the printed coordinate sequence
`(b_n)` is the printed Gram element of the corner representation `Θ`.

This is `manuscriptPrintedCoordinateGramRepresents` with the corona classes of
the `W_n` named as the values of `Θ`. -/
theorem correctedCornerSectorGramSequence_class (D : PrintedCornerData G model)
    (S : Finset G) (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    filterMatrixCStarCoronaMk (fun n ↦ D.cornerModel n) (ω : Filter ℕ)
        (correctedCornerSectorGramSequence D S)
      = unitaryGram S (fun s ↦
          ((correctedCornerCoronaRepresentation D ω hω s : unitary
              (FilterMatrixCStarCorona (fun n ↦ D.cornerModel n)
                (ω : Filter ℕ))) :
            FilterMatrixCStarCorona (fun n ↦ D.cornerModel n)
              (ω : Filter ℕ))) := by
  rw [manuscriptPrintedCoordinateGramRepresents G model D S (ω : Filter ℕ)]
  rfl

/-- **The printed corner-corona Kazhdan order, with `hclass` discharged.**

`exists_coordinateNormBound_of_cornerCoronaKazhdan` applied to the manuscript's
own data: the corner representation `Θ` is the class of the printed `(W_n)`,
the coordinate sequence is the printed `(b_n)`, and the hypothesis that the
latter represents the printed `b` is supplied by
`correctedCornerSectorGramSequence_class` rather than assumed.

The conclusion is verbatim the pair `(hrep, hnorm)` that
`eventually_sector_quadratic_form_ge` consumes. -/
theorem exists_coordinateNormBound_of_correctedCornerKazhdan
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (KD : KazhdanData G)
    (hno : ∀ y : CStarState.UniversalGNSSpace
        (FilterMatrixCStarCorona (fun n ↦ D.cornerModel n) (ω : Filter ℕ)),
      (∀ k : G, CStarState.universalGNSStarAlgHom
        ((correctedCornerCoronaRepresentation D ω hω k : unitary
          (FilterMatrixCStarCorona (fun n ↦ D.cornerModel n)
            (ω : Filter ℕ))) :
          FilterMatrixCStarCorona (fun n ↦ D.cornerModel n)
            (ω : Filter ℕ)) y = y) → y = 0) :
    ∃ (t : ℝ) (a : BoundedMatrixSequence (fun n ↦ D.cornerModel n)),
      (∀ n, a n = (t : ℂ) •
          (1 : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
          - sectorGram KD.S (fun s ↦
              (D.cornerMap n s :
                Matrix (D.cornerModel n) (D.cornerModel n) ℂ))) ∧
      ‖Ideal.Quotient.mk
          (nullMatrixSequenceIdeal (fun n ↦ D.cornerModel n) (ω : Filter ℕ)) a‖
        ≤ t - KD.kappa ^ 2 :=
  exists_coordinateNormBound_of_cornerCoronaKazhdan
    (fun n ↦ D.cornerModel n) (ω : Filter ℕ) KD.kazhdan.lowerUniverse
    (correctedCornerCoronaRepresentation D ω hω)
    (fun n s ↦ (D.cornerMap n s :
      Matrix (D.cornerModel n) (D.cornerModel n) ℂ))
    (correctedCornerSectorGramSequence D KD.S)
    (correctedCornerSectorGramSequence_apply D KD.S)
    (correctedCornerSectorGramSequence_class D KD.S ω hω) hno

/-- **The same, with the fixed-vector antecedent in its printed form.**  The
printed sentence before the one above is the vanishing of the corner Kazhdan
projection; `correctedCornerHilbertRepresentation_hasNoInvariantVectors` turns
it into `hno`.  With `hclass` proved, the only remaining input is
`CorrectedCornerKazhdanProjectionZero`. -/
theorem exists_coordinateNormBound_of_correctedCornerProjectionZero
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (KD : KazhdanData G)
    (hzero : CorrectedCornerKazhdanProjectionZero D ω hω KD) :
    ∃ (t : ℝ) (a : BoundedMatrixSequence (fun n ↦ D.cornerModel n)),
      (∀ n, a n = (t : ℂ) •
          (1 : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
          - sectorGram KD.S (fun s ↦
              (D.cornerMap n s :
                Matrix (D.cornerModel n) (D.cornerModel n) ℂ))) ∧
      ‖Ideal.Quotient.mk
          (nullMatrixSequenceIdeal (fun n ↦ D.cornerModel n) (ω : Filter ℕ)) a‖
        ≤ t - KD.kappa ^ 2 := by
  refine exists_coordinateNormBound_of_correctedCornerKazhdan D ω hω KD ?_
  intro y hy
  refine correctedCornerHilbertRepresentation_hasNoInvariantVectors
    D ω hω KD hzero y ?_
  intro g
  exact hy g

end KazhdanOrder

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
