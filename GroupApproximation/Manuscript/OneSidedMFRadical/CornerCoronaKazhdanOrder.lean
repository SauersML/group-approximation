import GroupApproximation.Manuscript.OneSidedMFRadical.FaithfulCornerNormBridge
import GroupApproximation.Manuscript.OneSidedMFRadical.FaithfulCornerCoronaRepresentation
import GroupApproximation.Analysis.MaximalCStarKazhdanProjection
import GroupApproximation.Analysis.UnitaryAverageFixedVector
import GroupApproximation.Analysis.GNSEigenvector

/-!
# The printed corner-corona Kazhdan operator order

`non_mf_groups_exist.tex`, third sentence of the printed proof of
`thm:normal-kazhdan`:

> Indeed, in every representation of the corner there are no `K`-fixed vectors,
> so the defining Kazhdan inequality gives this operator inequality,

the inequality being

    `b := |S|⁻¹ ∑_{s∈S} (qΘ(s)q - q)^*(qΘ(s)q - q) ≥ (κ²/|S|) q`

inside the corner of the norm-matrix corona.

`Manuscript/OneSidedMFRadical/CornerCoordinatePassage.lean` records under *What
is not claimed* that it derives no such order relation, and takes the norm form

    `∃ t : ℝ, ‖(t : ℂ) • 1 - b‖ ≤ t - κ²`

as the hypothesis `eventually_sector_quadratic_form_ge` consumes.  This module
produces that hypothesis from the printed antecedent.

## The route, and why it is the printed one

Three steps, each named separately so that a referee reading the printed
sentence can check them one at a time.

1. **The Gram element is a displacement sum.**  In any Hilbert-space
   representation, the quadratic form of
   `∑_{s∈S} (U_s - 1)^*(U_s - 1)` at a vector `x` is `∑_{s∈S} ‖U_s x - x‖²`
   (`re_inner_unitaryGram`).  This is where "the defining Kazhdan inequality"
   — a statement about vectors — and "this operator inequality" — a statement
   about an element of the algebra — meet: they are two readings of one
   identity.  It is also why the spelling of the order as a quadratic form in
   `PrintedSectorProof` loses no information.

2. **The Kazhdan inequality.**  If the represented group has no nonzero fixed
   vector, `complex_kazhdan_sum_sq_ge_of_noInvariant` bounds that displacement
   sum below by `κ²‖x‖²`
   (`kappa_sq_mul_norm_sq_le_re_inner_unitaryGram`).  The "no `K`-fixed
   vectors" clause is the printed antecedent, and §4 below discharges it from
   the printed sentence that precedes it — the vanishing of the Kazhdan
   projection in the corner.

3. **A faithful representation converts the vector bound into the norm form.**
   `Analysis/CStarStateGNS.lean` makes the GNS representations of the states of
   a nontrivial unital `C*`-algebra a jointly isometric family, and
   `FaithfulCornerCoronaRepresentation.lean` assembles them into the single
   faithful `⋆`-representation `CStarState.universalGNSStarAlgHom` on their
   Hilbert `ℓ²`-sum.  `normFormLowerBound_of_faithful_quadraticForm`
   (`FaithfulCornerNormBridge.lean`) then turns the quadratic-form bound in
   that representation into `‖t·1 - b‖ ≤ t - κ²` in the algebra, by the
   numerical-range estimate and isometry — no order instance, no continuous
   functional calculus, no order-reflection theorem.

The composite is `cornerCorona_kazhdan_normForm`, stated for an arbitrary
nontrivial unital `C*`-algebra, since nothing in the printed sentence uses that
the corner is a matrix corona.  `exists_coordinateNormBound_of_cornerCoronaKazhdan`
specialises it to the corona and delivers exactly the pair `(hrep, hnorm)` that
`eventually_sector_quadratic_form_ge` consumes;
`eventually_sector_quadratic_form_ge_of_cornerCoronaKazhdan` performs that
composition, so the printed chain now runs from the Kazhdan pair to the
coordinate inequality with no order hypothesis left in between.

## What is proved

* `unitaryGram`, `isSelfAdjoint_unitaryGram` — the printed positive element
  `b = ∑_{s∈S} (Θ(s) - 1)^*(Θ(s) - 1)` in a `⋆`-ring, and its self-adjointness.
* `re_inner_unitaryGram` — its quadratic form is the printed displacement sum.
* `kappa_sq_mul_norm_sq_le_re_inner_unitaryGram` — the defining Kazhdan
  inequality, read on that quadratic form, for a unitary representation with no
  nonzero fixed vector.
* `kazhdan_quadraticForm_universalGNS` — the same in the universal GNS
  representation of the algebra, which is the "every representation of the
  corner" of the printed sentence in its jointly isometric form.
* `cornerCorona_kazhdan_normForm` — **the printed sentence**: the operator
  order `b ≥ κ²·1`, in the norm form `∃ t, ‖t·1 - b‖ ≤ t - κ²`, inside the
  algebra.
* `exists_maximalProjectionLift_fixedVector_iff`,
  `KazhdanProjectionImageZero`,
  `noInvariantVectors_of_kazhdanProjectionImageZero` — the antecedent, from the
  printed sentence before it: in a Hilbert-space representation the image of
  the `Cmax(K)` Kazhdan projection is the projection onto the fixed vectors, so
  if that image vanishes — which is what "in the corner the Kazhdan projection
  is zero" says once the corner is represented — the representation has no
  nonzero fixed vector.
* `exists_coordinateNormBound_of_cornerCoronaKazhdan`,
  `eventually_sector_quadratic_form_ge_of_cornerCoronaKazhdan` — the corona
  specialisation, in the exact shape `CornerCoordinatePassage` consumes, and
  the composition with it.
* `PrintedCornerCoronaKazhdanOrder` /
  `manuscriptPrintedCornerCoronaKazhdanOrder` — the three of them as one
  proposition with every quantifier and hypothesis inside the statement.

## What is not claimed

That the corner of the corona *has* no nonzero `K`-fixed vector.  Every
statement below carries that as an explicit antecedent, in one of its two
equivalent forms: directly (`hno`), or as the vanishing of the image of the
`Cmax(K)` Kazhdan projection (`KazhdanProjectionImageZero`), which
`noInvariantVectors_of_kazhdanProjectionImageZero` proves implies it.  Nothing
here derives the vanishing itself for the manuscript's corner: that is the
compression identity `q p q = 0` of `corner_compression_kazhdanProjection`
transported along the `⋆`-homomorphism `Cmax(K) → q 𝒬 q`, and the corner
algebra `q 𝒬 q` is not constructed in this repository.  The corrected-corner
lane carries the same residue under the name
`CorrectedCornerKazhdanProjectionZero`
(`CorrectedCornerKazhdanQuadraticBridge.lean`); the statements below are the
lane-independent form of it.

Consequently `manuscriptPrintedCornerCoronaKazhdanOrder` is a closed proof of
an *implication*: the antecedent is inside the proposition, not in front of it.

## Manuscript status

Supplies the printed sentence "in every representation of the corner there are
no `K`-fixed vectors, so the defining Kazhdan inequality gives this operator
inequality" of the proof of `thm:normal-kazhdan`, as the implication the
printed proof states, and composes it with the corona-to-coordinate passage.
The endpoint of `thm:normal-kazhdan` itself is unchanged and remains
`CoronaImageNormalKazhdan`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open AbstractSpectralGap GNSEigenvector
open MaximalCStarKazhdanProjection
open UnitaryAverageFixedVector
open UltraproductKazhdanProjection
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

universe u v w

/-! ## The printed positive element

`unitaryGram S U = ∑_{s∈S} (U_s - 1)^*(U_s - 1)`.  With `U = Θ` the corner
representation and `1 = q` the identity of the corner, this is the printed
`b` with the factor `|S|⁻¹` left off — the same normalization convention as
`sectorGram` in `CornerCoordinatePassage`, which carries `|S|` on the right and
restores the printed constant at the trace step. -/

/-- The printed Gram element `b = ∑_{s∈S} (Θ(s) - 1)^*(Θ(s) - 1)` of a
`⋆`-ring. -/
def unitaryGram {ι : Type*} {A : Type*} [Ring A] [StarRing A] (S : Finset ι)
    (U : ι → A) : A :=
  ∑ s ∈ S, star (U s - 1) * (U s - 1)

/-- The printed Gram element is self-adjoint: it is a sum of elements of the
form `x^* x`. -/
theorem isSelfAdjoint_unitaryGram {ι : Type*} {A : Type*} [Ring A] [StarRing A]
    (S : Finset ι) (U : ι → A) : IsSelfAdjoint (unitaryGram S U) := by
  rw [IsSelfAdjoint, unitaryGram, star_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [star_mul, star_star]

/-- **The quadratic form of the printed Gram element is the printed
displacement sum.**  In a Hilbert space, `star` is the adjoint, so

    `re ⟪x, ∑_{s∈S} (U_s - 1)^*(U_s - 1) x⟫ = ∑_{s∈S} ‖U_s x - x‖²`.

This identity is the whole content of "the defining Kazhdan inequality gives
this operator inequality": the left-hand side is the operator order in its
instance-free reading, the right-hand side is what a Kazhdan pair bounds. -/
theorem re_inner_unitaryGram {ι : Type*} {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (S : Finset ι)
    (U : ι → (E →L[ℂ] E)) (x : E) :
    (⟪x, unitaryGram S U x⟫_ℂ).re = ∑ s ∈ S, ‖U s x - x‖ ^ 2 := by
  rw [unitaryGram, _root_.sum_apply, inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact CStarTensor.re_inner_self _

/-! ## The defining Kazhdan inequality, on the printed Gram element

The corner carries no nonzero `K`-fixed vector, so the Kazhdan pair applies and
bounds the displacement sum below by `κ²‖x‖²`.  Restriction of scalars is
already done in `CornerCoordinatePassage`
(`complex_kazhdan_sum_sq_ge_of_noInvariant`), at no loss in either the control
set or the constant. -/

/-- **The printed operator inequality, in quadratic form.**  If a unitary
representation of `K` on a complex Hilbert space has no nonzero fixed vector,
then the Kazhdan pair `(S, κ)` forces

    `κ²‖x‖² ≤ re ⟪x, ∑_{s∈S} (ρ(s) - 1)^*(ρ(s) - 1) x⟫`

for every vector `x`.  This is exactly the printed sentence, at the level of
one representation. -/
theorem kappa_sq_mul_norm_sq_le_re_inner_unitaryGram {K : Type w} [Group K]
    {S : Finset K} {kappa : ℝ} (hS : IsKazhdanPair.{w, v} K S kappa)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (rho : K →* unitary (E →L[ℂ] E))
    (hno : ∀ y : E,
      (∀ k : K, ((rho k : unitary (E →L[ℂ] E)) : E →L[ℂ] E) y = y) → y = 0)
    (x : E) :
    kappa ^ 2 * ‖x‖ ^ 2
      ≤ (⟪x, unitaryGram S
          (fun s ↦ ((rho s : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) x⟫_ℂ).re := by
  rw [re_inner_unitaryGram]
  exact complex_kazhdan_sum_sq_ge_of_noInvariant hS
    (unitaryIsometryHom.comp rho) (fun y hy ↦ hno y hy) x

/-! ## "In every representation of the corner"

`Analysis/CStarStateGNS.lean` supplies a family of GNS representations that is
jointly isometric, and `FaithfulCornerCoronaRepresentation.lean` assembles it
into one faithful `⋆`-representation on the Hilbert `ℓ²`-sum of the GNS spaces.
That is the printed "every representation of the corner" in the only form the
argument uses: a single representation that loses nothing. -/

/-- **The printed inequality in the universal GNS representation.**  The image
of the printed Gram element under the faithful direct-sum GNS representation is
the Gram element of the represented unitaries, so the previous theorem applies
verbatim. -/
theorem kazhdan_quadraticForm_universalGNS {A : Type u} [CStarAlgebra A]
    [Nontrivial A] {K : Type w} [Group K] {S : Finset K} {kappa : ℝ}
    (hS : IsKazhdanPair.{w, u} K S kappa) (Theta : K →* unitary A)
    (hno : ∀ y : CStarState.UniversalGNSSpace A,
      (∀ k : K, CStarState.universalGNSStarAlgHom
        ((Theta k : unitary A) : A) y = y) → y = 0)
    (x : CStarState.UniversalGNSSpace A) :
    kappa ^ 2 * ‖x‖ ^ 2
      ≤ (⟪x, CStarState.universalGNSStarAlgHom
          (unitaryGram S fun s ↦ ((Theta s : unitary A) : A)) x⟫_ℂ).re := by
  have hmap : CStarState.universalGNSStarAlgHom
        (unitaryGram S fun s ↦ ((Theta s : unitary A) : A))
      = (unitaryGram S fun s ↦ CStarState.universalGNSStarAlgHom
          ((Theta s : unitary A) : A)) := by
    simp only [unitaryGram, map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [map_mul, map_star, map_sub, map_one]
  rw [hmap]
  exact kappa_sq_mul_norm_sq_le_re_inner_unitaryGram hS
    ((unitaryMap (CStarState.universalGNSStarAlgHom (A := A))).comp Theta)
    (fun y hy ↦ hno y hy) x

/-- **The printed sentence.**  Let `(S, κ)` be a Kazhdan pair for `K` and let
`Θ : K → U(A)` be a unitary representation in a nontrivial unital
`C*`-algebra — for the manuscript, the corner of the norm-matrix corona.  If
the corner carries no nonzero `K`-fixed vector, then the printed positive
element

    `b = ∑_{s∈S} (Θ(s) - 1)^*(Θ(s) - 1)`

satisfies the operator order `b ≥ κ²·1`, written in the norm form that a
unital `C*`-algebra always has for a bounded self-adjoint element:

    `∃ t : ℝ, ‖t·1 - b‖ ≤ t - κ²`.

That is verbatim the corona-level hypothesis `CornerCoordinatePassage.lean`
lists under *What is not claimed*.  The witness is the explicit
`t = ‖b - κ²·1‖ + κ²`.

The hypothesis `hno` is the printed antecedent "in every representation of the
corner there are no `K`-fixed vectors", read in the jointly isometric GNS
family; `noInvariantVectors_of_kazhdanProjectionImageZero` below derives it
from the printed sentence before it. -/
theorem cornerCorona_kazhdan_normForm {A : Type u} [CStarAlgebra A]
    [Nontrivial A] {K : Type w} [Group K] {S : Finset K} {kappa : ℝ}
    (hS : IsKazhdanPair.{w, u} K S kappa) (Theta : K →* unitary A)
    (hno : ∀ y : CStarState.UniversalGNSSpace A,
      (∀ k : K, CStarState.universalGNSStarAlgHom
        ((Theta k : unitary A) : A) y = y) → y = 0) :
    ∃ t : ℝ,
      ‖(t : ℂ) • (1 : A) -
          (unitaryGram S fun s ↦ ((Theta s : unitary A) : A))‖
        ≤ t - kappa ^ 2 := by
  refine ⟨‖(unitaryGram S fun s ↦ ((Theta s : unitary A) : A))
    - ((kappa ^ 2 : ℝ) : ℂ) • (1 : A)‖ + kappa ^ 2, ?_⟩
  exact normFormLowerBound_of_faithful_quadraticForm
    (CStarState.universalGNSStarAlgHom (A := A))
    (CStarState.universalGNSStarAlgHom_injective (A := A))
    (isSelfAdjoint_unitaryGram S fun s ↦ ((Theta s : unitary A) : A))
    (kappa ^ 2) (kazhdan_quadraticForm_universalGNS hS Theta hno)

/-! ## The antecedent: no fixed vectors, from the vanishing Kazhdan projection

> In the corner `q 𝒬_d q`, the Kazhdan projection is zero.  …  Indeed, in every
> representation of the corner there are no `K`-fixed vectors.

`Analysis/MaximalCStarKazhdanProjection.lean` builds the Kazhdan projection
once, inside `Cmax(K)`, and identifies its image under a `⋆`-homomorphism with
the spectral projection of the orbit average of the image representation;
`Analysis/UnitaryAverageFixedVector.lean` identifies the range of that spectral
projection with the fixed vectors.  Composing the two, the image of the
`Cmax(K)` Kazhdan projection in `B(E)` is the projection onto the `K`-fixed
vectors of `E`, so its vanishing says precisely that there are none.

`SentenceNormalKazhdanClosure.manuscriptSentence171_maximalProjectionImageIsFixedProjection`
already records the identification at the single Hilbert-space universe
`u + 1`; the version below is the same proof with the representation universe
left free, which is what the corner corona needs — its universal GNS space
lives in the universe of the corona, not one above the group. -/

/-- **The image of the `Cmax(K)` Kazhdan projection is the fixed-vector
projection**, at an arbitrary Hilbert-space universe.

`D.kazhdan` is stored at the universe of `Cmax(K)`; the Kazhdan pair at the
universe of `E` is taken as the separate hypothesis `hS`, since universe
descent for property `(T)` is not available in that direction. -/
theorem exists_maximalProjectionLift_fixedVector_iff {K : Type w} [Group K]
    (D : KazhdanData K) {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (hS : IsKazhdanPair.{w, v} K D.S D.kappa)
    (rho : K →* unitary (E →L[ℂ] E)) :
    ∃ f : MaximalGroupCStar K →⋆ₐ[ℂ] (E →L[ℂ] E),
      (∀ k : K, f (maximalGroupCStarGenerator K k) =
        ((rho k : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) ∧
      ∀ x : E, f D.projection x = x ↔
        ∀ k : K, ((rho k : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x := by
  obtain ⟨f, hf, _hunique⟩ :=
    maximalGroupCStar_existsUnique_lift_allUniverses K rho
  refine ⟨f, hf, ?_⟩
  have hgap : ∀ mu ∈ spectrum ℝ (unitaryAverage rho D.S),
      mu ≤ D.rate ∨ mu = 1 := by
    intro mu hmu
    by_cases hmu1 : mu = 1
    · exact Or.inr hmu1
    · left
      have hmuC : (mu : ℂ) ∈ spectrum ℂ (unitaryAverage rho D.S) := by
        have h := spectrum.algebraMap_mem ℂ hmu
        rwa [show (algebraMap ℝ ℂ) mu = (mu : ℂ) by simp] at h
      exact unitaryAverage_spectrum_le_manuscript rho hS D.S
        Finset.Subset.rfl D.one_mem D.symm hmuC hmu1
  have himage : f D.projection =
      CStarSpectralProjection.spectralProjection
        (unitaryAverage rho D.S) D.rate :=
    image_eq_spectralProjection D rho f hf hgap
  intro x
  rw [himage, spectralProjection_apply_eq_self_iff rho
    ⟨1, D.one_mem⟩ D.symm D.rate_lt_one hgap x]
  constructor
  · intro h k
    apply apply_eq_self_of_mem_closure rho (fun s hs ↦ h s hs)
    rw [D.generates]
    trivial
  · intro h s _hs
    exact h s

/-- **"In the corner `q 𝒬_d q`, the Kazhdan projection is zero", represented.**
The image of the `Cmax(K)` Kazhdan projection under every `⋆`-homomorphism
carrying the canonical unitaries to `ρ` vanishes.

Stated for all lifts rather than for one, because the lift is produced
existentially by the universal property of `Cmax(K)`; by its uniqueness clause
the two readings agree. -/
def KazhdanProjectionImageZero {K : Type w} [Group K] (D : KazhdanData K)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (rho : K →* unitary (E →L[ℂ] E)) : Prop :=
  ∀ f : MaximalGroupCStar K →⋆ₐ[ℂ] (E →L[ℂ] E),
    (∀ k : K, f (maximalGroupCStarGenerator K k) =
      ((rho k : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) →
    f D.projection = 0

/-- **"…so in every representation of the corner there are no `K`-fixed
vectors."**  A vector fixed by the whole group is fixed by the image of the
Kazhdan projection, which is zero; so it is zero. -/
theorem noInvariantVectors_of_kazhdanProjectionImageZero {K : Type w} [Group K]
    (D : KazhdanData K) {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (hS : IsKazhdanPair.{w, v} K D.S D.kappa)
    (rho : K →* unitary (E →L[ℂ] E))
    (hzero : KazhdanProjectionImageZero D rho) :
    ∀ y : E,
      (∀ k : K, ((rho k : unitary (E →L[ℂ] E)) : E →L[ℂ] E) y = y) → y = 0 := by
  obtain ⟨f, hf, hfix⟩ :=
    exists_maximalProjectionLift_fixedVector_iff D hS rho
  have hpzero : f D.projection = 0 := hzero f hf
  intro y hy
  have hpy : f D.projection y = y := (hfix y).2 hy
  rw [hpzero] at hpy
  simpa using hpy.symm

/-! ## The corona specialisation

`CornerCoordinatePassage.eventually_sector_quadratic_form_ge` consumes a pair:
a bounded matrix sequence `a` with `a n = t·1 - b_n` at every coordinate, and
the corona norm bound `‖[a]‖ ≤ t - c`.  `FaithfulCornerNormBridge` builds that
pair from a quadratic-form bound in a faithful representation; feeding it the
Kazhdan bound above removes the last analytic hypothesis. -/

/-- **The printed sentence at the corona, in the shape the coordinate passage
consumes.**  `hbseq` says the bounded sequence `bseq` is the printed coordinate
element `b_n = ∑_{s∈S}(W_n(s) - q_n)^*(W_n(s) - q_n)`, `hclass` says its corona
class is the printed `b`, and `hno` is the printed "no `K`-fixed vectors".  The
conclusion is verbatim the pair `(hrep, hnorm)` of
`eventually_sector_quadratic_form_ge`. -/
theorem exists_coordinateNormBound_of_cornerCoronaKazhdan (X : ℕ → Type u)
    [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]
    (l : Filter ℕ) [Filter.NeBot l]
    [Nontrivial (FilterMatrixCStarCorona X l)]
    {K : Type w} [Group K] {S : Finset K} {kappa : ℝ}
    (hS : IsKazhdanPair.{w, u} K S kappa)
    (Theta : K →* unitary (FilterMatrixCStarCorona X l))
    (W : ∀ n, K → Matrix (X n) (X n) ℂ) (bseq : BoundedMatrixSequence X)
    (hbseq : ∀ n, bseq n = sectorGram S (W n))
    (hclass : filterMatrixCStarCoronaMk X l bseq =
      (unitaryGram S fun s ↦
        ((Theta s : unitary (FilterMatrixCStarCorona X l)) :
          FilterMatrixCStarCorona X l)))
    (hno : ∀ y : CStarState.UniversalGNSSpace (FilterMatrixCStarCorona X l),
      (∀ k : K, CStarState.universalGNSStarAlgHom
        ((Theta k : unitary (FilterMatrixCStarCorona X l)) :
          FilterMatrixCStarCorona X l) y = y) → y = 0) :
    ∃ (t : ℝ) (a : BoundedMatrixSequence X),
      (∀ n, a n =
        (t : ℂ) • (1 : Matrix (X n) (X n) ℂ) - sectorGram S (W n)) ∧
      ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖ ≤ t - kappa ^ 2 := by
  refine exists_coordinateNormBound_of_faithful_cornerKazhdan X l S W bseq hbseq
    (CStarState.universalGNSStarAlgHom (A := FilterMatrixCStarCorona X l))
    (CStarState.universalGNSStarAlgHom_injective
      (A := FilterMatrixCStarCorona X l))
    (kappa ^ 2) ?_
  intro x
  rw [hclass]
  exact kazhdan_quadraticForm_universalGNS hS Theta hno x

/-- **The printed sentence composed with the corona-to-coordinate passage.**
With the operator order supplied rather than assumed, the coordinate
quadratic-form inequality of `PrintedSectorProof` holds — with the printed
`o(1)` carried by `ε` — at every coordinate of a set in the filter.

This is the composition `CornerCoordinatePassage` was written for: its
`eventually_sector_quadratic_form_ge` no longer needs a corona-order
hypothesis, only the Kazhdan pair and the printed "no `K`-fixed vectors". -/
theorem eventually_sector_quadratic_form_ge_of_cornerCoronaKazhdan
    (X : ℕ → Type u) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)] (l : Filter ℕ) [Filter.NeBot l]
    [Nontrivial (FilterMatrixCStarCorona X l)]
    {K : Type w} [Group K] {S : Finset K} {kappa : ℝ}
    (hS : IsKazhdanPair.{w, u} K S kappa)
    (Theta : K →* unitary (FilterMatrixCStarCorona X l))
    (W : ∀ n, K → Matrix (X n) (X n) ℂ) (bseq : BoundedMatrixSequence X)
    (hbseq : ∀ n, bseq n = sectorGram S (W n))
    (hclass : filterMatrixCStarCoronaMk X l bseq =
      (unitaryGram S fun s ↦
        ((Theta s : unitary (FilterMatrixCStarCorona X l)) :
          FilterMatrixCStarCorona X l)))
    (hno : ∀ y : CStarState.UniversalGNSSpace (FilterMatrixCStarCorona X l),
      (∀ k : K, CStarState.universalGNSStarAlgHom
        ((Theta k : unitary (FilterMatrixCStarCorona X l)) :
          FilterMatrixCStarCorona X l) y = y) → y = 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in l, ∀ x : X n → ℂ,
      (kappa ^ 2 - epsilon) * ∑ i : X n, Complex.normSq (x i)
        ≤ ∑ s ∈ S, ∑ i : X n, Complex.normSq ((W n s *ᵥ x - x) i) := by
  obtain ⟨t, a, hrep, hnorm⟩ :=
    exists_coordinateNormBound_of_cornerCoronaKazhdan X l hS Theta W bseq hbseq
      hclass hno
  exact eventually_sector_quadratic_form_ge X l S W a t (kappa ^ 2) hrep hnorm
    hepsilon

/-! ## The printed sentence as one closed proposition -/

/-- **The printed sentence "in every representation of the corner there are no
`K`-fixed vectors, so the defining Kazhdan inequality gives this operator
inequality", as one proposition**, in three clauses:

1. the operator order itself, in a nontrivial unital `C*`-algebra: from a
   Kazhdan pair and the absence of nonzero fixed vectors in the universal GNS
   representation, the printed Gram element `b` satisfies
   `∃ t, ‖t·1 - b‖ ≤ t - κ²`, which is the norm form of `b ≥ κ²·1`;
2. the antecedent, from the printed sentence before it: if the image of the
   `Cmax(K)` Kazhdan projection vanishes in a Hilbert-space representation,
   that representation has no nonzero fixed vector;
3. the corona specialisation: the same order, delivered as the coordinate
   representative and corona norm bound that
   `eventually_sector_quadratic_form_ge` consumes.

Clause 1 takes the absence of fixed vectors as an antecedent rather than
deriving it: for the manuscript's corner that is the compression identity
`q p q = 0` transported to the corner algebra `q 𝒬 q`, which this repository
does not construct.  See *What is not claimed* in the module docstring. -/
def PrintedCornerCoronaKazhdanOrder : Prop :=
  (∀ (K : Type) [Group K] (S : Finset K) (kappa : ℝ),
      IsKazhdanPair.{0, 0} K S kappa →
      ∀ (A : Type) [CStarAlgebra A] [Nontrivial A] (Theta : K →* unitary A),
        (∀ y : CStarState.UniversalGNSSpace A,
          (∀ k : K, CStarState.universalGNSStarAlgHom
            ((Theta k : unitary A) : A) y = y) → y = 0) →
        ∃ t : ℝ,
          ‖(t : ℂ) • (1 : A) -
              (unitaryGram S fun s ↦ ((Theta s : unitary A) : A))‖
            ≤ t - kappa ^ 2) ∧
    (∀ (K : Type) [Group K] (D : KazhdanData K) (E : Type)
        [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E],
        IsKazhdanPair.{0, 0} K D.S D.kappa →
        ∀ rho : K →* unitary (E →L[ℂ] E),
          KazhdanProjectionImageZero D rho →
          ∀ y : E,
            (∀ k : K, ((rho k : unitary (E →L[ℂ] E)) : E →L[ℂ] E) y = y) →
            y = 0) ∧
    (∀ (X : ℕ → Type) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
        [∀ n, Nonempty (X n)] (l : Filter ℕ) [Filter.NeBot l]
        [Nontrivial (FilterMatrixCStarCorona X l)]
        (K : Type) [Group K] (S : Finset K) (kappa : ℝ),
        IsKazhdanPair.{0, 0} K S kappa →
        ∀ (Theta : K →* unitary (FilterMatrixCStarCorona X l))
          (W : ∀ n, K → Matrix (X n) (X n) ℂ)
          (bseq : BoundedMatrixSequence X),
          (∀ n, bseq n = sectorGram S (W n)) →
          filterMatrixCStarCoronaMk X l bseq =
            (unitaryGram S fun s ↦
              ((Theta s : unitary (FilterMatrixCStarCorona X l)) :
                FilterMatrixCStarCorona X l)) →
          (∀ y : CStarState.UniversalGNSSpace (FilterMatrixCStarCorona X l),
            (∀ k : K, CStarState.universalGNSStarAlgHom
              ((Theta k : unitary (FilterMatrixCStarCorona X l)) :
                FilterMatrixCStarCorona X l) y = y) → y = 0) →
          ∃ (t : ℝ) (a : BoundedMatrixSequence X),
            (∀ n, a n =
              (t : ℂ) • (1 : Matrix (X n) (X n) ℂ) - sectorGram S (W n)) ∧
            ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖
              ≤ t - kappa ^ 2)

/-- Closed proof of the printed corner-corona Kazhdan operator order. -/
theorem manuscriptPrintedCornerCoronaKazhdanOrder :
    PrintedCornerCoronaKazhdanOrder := by
  refine ⟨?_, ?_, ?_⟩
  · intro K _ S kappa hS A _ _ Theta hno
    exact cornerCorona_kazhdan_normForm hS Theta hno
  · intro K _ D E _ _ _ hS rho hzero
    exact noInvariantVectors_of_kazhdanProjectionImageZero D hS rho hzero
  · intro X _ _ _ l _ _ K _ S kappa hS Theta W bseq hbseq hclass hno
    exact exists_coordinateNormBound_of_cornerCoronaKazhdan X l hS Theta W bseq
      hbseq hclass hno

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
