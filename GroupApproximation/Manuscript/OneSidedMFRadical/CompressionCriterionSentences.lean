import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanPrintedRoute
import GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCornerPrintedRoute
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanTransportSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.TransportCommutantEquality
import GroupApproximation.Manuscript.OneSidedMFRadical.TransportPrintedCommutant
import GroupApproximation.Manuscript.OneSidedMFRadical.DefectHS
import GroupApproximation.Manuscript.OneSidedMFRadical.FiniteDimensionalCommutant
import GroupApproximation.Manuscript.OneSidedMFRadical.StableFiniteness
import GroupApproximation.Sofic.UltraproductAdjointAmbient

/-!
# The analytic printed sentences the census cannot match on its own

`non_mf_groups_exist.tex`.  One declaration per printed sentence, for four
blocks whose sentences carry analytic content that no single existing
declaration states in the printed words:

* the paragraph of the introduction that outlines the proof of
  `thm:compression-criterion` (seven sentences);
* the setup paragraph of "Kazhdan transport in normalized Hilbert--Schmidt
  norm", before the proof of `thm:transport` (three sentences);
* the printed proof of `cor:defect-hs` (three sentences);
* the one setup sentence of "From Hilbert--Schmidt to operator norm".

Every declaration here is a wrapper: the mathematics is already on `main`, and
the docstring names the module that owns it.  Only one lemma is new,
`conjugatedMap_opNormVanishing`, and it is new because nothing in the tree
states the operator-norm vanishing of `V_n(u) V_n(c) V_n(u)^* - V_n(ucu^{-1})`
on its own -- the corpus always produced that estimate inline, inside the
corner argument of `Sofic/KazhdanCompressorCorner.lean`.

The printed `Ad(V_n(g))` is the repository's `conjDouble (V.map n g)`, the
matrix of `xi -> V_n(g) xi V_n(g)^*` in row-major matrix units; the printed
ambient `𝓑` with coordinate sizes `d_n^2` is
`NormMatrixCStarCorona (fun n => V.adjoint.model n)`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace CompressionCriterionSentences

open Matrix
open MaximalCStarKazhdanProjection
open KazhdanAsymptoticCommutant
open KazhdanCornerMatrices
open PrintedCornerCompression
open NormalKazhdanPrintedRoute
open TransportPrintedCommutant
open scoped Matrix.Norms.L2Operator commutatorElement

noncomputable section

universe u v w

/-! ## `thm:compression-criterion`: the seven sentences of the printed outline -/

/-- **`thm:compression-criterion`, sentence `5c4b238d20db`.**

> Asymptotic multiplicativity in operator norm makes the conjugation maps
> `Ad(V_n(g)) : x ↦ V_n(g) x V_n(g)*` an asymptotically multiplicative family
> of unitaries on `M_{d_n}(ℂ)` with its normalized Hilbert--Schmidt inner
> product.

Four conjuncts, one per clause of the sentence.  The conjugation reading is
`kt_01_adjoint_action`: in row-major coordinates `x ↦ V_n(g) x V_n(g)*` is the
matrix `conjDouble (V_n(g))`, which is the coordinate matrix of the adjoint
almost representation.  "Unitaries ... with its normalized Hilbert--Schmidt
inner product" is `kt_01_hsNormSq_adjoint`, the invariance of `‖·‖₂` under the
conjugation.  "Asymptotically multiplicative" is
`kt_01_adjoint_asymptoticallyMultiplicative`, which is dimension-free.  All
four facts live in `Sofic/UltraproductAdjointAmbient.lean` and
`Sofic/AdjointMatrix.lean`; the sentence is their conjunction. -/
theorem manuscriptSentence_adIsAsymptoticallyMultiplicativeUnitaryFamily
    {G : Type} [Group G] (V : OpAlmostRepresentation G) :
    (∀ (n : ℕ) (g : G) (xi : Matrix (V.model n) (V.model n) ℂ),
        conjDouble (V.map n g : Matrix (V.model n) (V.model n) ℂ) *ᵥ rowVec xi
          = rowVec ((V.map n g : Matrix (V.model n) (V.model n) ℂ) * xi *
              (V.map n g : Matrix (V.model n) (V.model n) ℂ)ᴴ)) ∧
      (∀ (n : ℕ) (g : G),
        (V.adjoint.map n g :
            Matrix (V.adjoint.model n) (V.adjoint.model n) ℂ)
          = conjDouble (V.map n g : Matrix (V.model n) (V.model n) ℂ)) ∧
      (∀ (n : ℕ) (g : G) (xi : Matrix (V.model n) (V.model n) ℂ),
        hsNormSq (V.model n)
            ((V.map n g : Matrix (V.model n) (V.model n) ℂ) * xi *
              (V.map n g : Matrix (V.model n) (V.model n) ℂ)ᴴ)
          = hsNormSq (V.model n) xi) ∧
      (∀ (g h : G) (ε : ℝ), 0 < ε → ∃ N, ∀ n ≥ N,
        ‖(V.adjoint.map n (g * h) :
              Matrix (V.adjoint.model n) (V.adjoint.model n) ℂ) -
            (V.adjoint.map n g :
                Matrix (V.adjoint.model n) (V.adjoint.model n) ℂ) *
              (V.adjoint.map n h :
                Matrix (V.adjoint.model n) (V.adjoint.model n) ℂ)‖ ≤ ε) :=
  ⟨fun n g xi ↦ kt_01_adjoint_action (V.model n)
      ((V.map n g : Matrix (V.model n) (V.model n) ℂ)) xi,
    fun n g ↦ kt_01_adjoint_map V n g,
    fun n g xi ↦ kt_01_hsNormSq_adjoint (V.model n) (V.map n g).2
      (V.modelNonempty n) xi,
    fun g h ε hε ↦
      kt_01_adjoint_asymptoticallyMultiplicative V g h (ε := ε) hε⟩

/-- **`thm:compression-criterion`, sentence `b529b81ba1b5`.**

> Here `‖Ad(A) - Ad(B)‖ ≤ 2‖A - B‖`, with the norm on the left taken in the
> operator algebra of this Hilbert space.

`Sofic/AdjointMatrix.lean` owns the estimate as `l2_opNorm_conjDouble_sub_le_two`.
The printed sentence is stated for the conjugation maps of the surrounding
paragraph, so both arguments are unitary; the repository lemma carries exactly
those hypotheses, and the norm on the left is the `l2` operator norm on the
doubled index type, which is the operator algebra of the matrix Hilbert
space. -/
theorem manuscriptSentence_adIsTwoLipschitz
    {Y : FiniteModel} {A B : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (hB : B ∈ Matrix.unitaryGroup Y ℂ) :
    ‖conjDouble A - conjDouble B‖ ≤ 2 * ‖A - B‖ :=
  l2_opNorm_conjDouble_sub_le_two hA hB

/-- **`thm:compression-criterion`, sentence `7cb15e1cfb7c`.**

> The classes of these maps form a homomorphism of `G` into the unitary group
> of the norm matrix corona with coordinate sizes `d_n^2`.

`adjointCoronaHom` of `Sofic/UltraproductAdjointAmbient.lean` is that
homomorphism; the first two conjuncts are its defining formula and its
multiplicativity.  The third conjunct is the printed "coordinate sizes
`d_n^2`": the models of the adjoint almost representation are the doubled
models, whose cardinality is `card (V.model n) ^ 2`.  That last clause is what
distinguishes this sentence from `thm:transport`'s `354d89cc595c`
(`manuscriptSentence_sigmaTildeIsHomomorphism`), which states the homomorphism
property without pinning the coordinate size. -/
theorem manuscriptSentence_adClassesFormCoronaHomomorphism
    {G : Type} [Group G] (V : OpAlmostRepresentation G)
    [∀ n, Nonempty (V.adjoint.model n)] :
    (∀ g : G, adjointCoronaHom V g =
        unitarySequenceToCorona V.adjoint.model
          (fun n ↦ V.adjoint.map n g)) ∧
      (∀ g h : G, adjointCoronaHom V (g * h)
          = adjointCoronaHom V g * adjointCoronaHom V h) ∧
      (∀ n : ℕ, Fintype.card (V.adjoint.model n)
          = Fintype.card (V.model n) * Fintype.card (V.model n)) :=
  ⟨fun g ↦ adjointCoronaHom_apply V g,
    fun g h ↦ map_mul (adjointCoronaHom V) g h,
    fun n ↦ card_doubleModel (V.model n)⟩

/-- **`thm:compression-criterion`, sentence `8c90718559ac`.**

> Let `U` be the class of `(Ad(V_n(u)))` and `P` the image of the Kazhdan
> projection of `L` in that corona.

The sentence names two objects, and both namings are the content.  `U` is the
corona class of the adjoint sequence at `u`, which is the value of
`adjointCoronaHom` there.  `P` is the image of the Kazhdan projection under
the extension of `σ̃|_L` to `C*_max(L)`: property `(T)` supplies the projection
(`exists_kazhdanData`), the universal property supplies the extension
(`maximalGroupCStar_existsUnique_lift_allUniverses`), and the image is a
projection (`isStarProjection_image`).  Nothing is asserted about `P` beyond
its existence and its being a projection; the order relation `U* P U ≤ P` is
the next printed sentence, already carried by
`manuscriptSentence_movedFixedSpaceInclusionAndProjectionOrder`. -/
theorem manuscriptSentence_compressorClassAndKazhdanProjectionImage
    {G : Type} [Group G] (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (V : OpAlmostRepresentation G) [∀ n, Nonempty (V.adjoint.model n)]
    (u : G) :
    adjointCoronaHom V u
        = unitarySequenceToCorona V.adjoint.model
            (fun n ↦ V.adjoint.map n u) ∧
      ∃ (D : KazhdanData ↥L)
        (f : MaximalGroupCStar ↥L →⋆ₐ[ℂ]
          NormMatrixCStarCorona (fun n ↦ V.adjoint.model n)),
        (∀ l : ↥L, f (maximalGroupCStarGenerator ↥L l)
            = ((adjointCoronaHom V (l : G) :
                unitary (NormMatrixCStarCorona (fun n ↦ V.adjoint.model n))) :
              NormMatrixCStarCorona (fun n ↦ V.adjoint.model n))) ∧
          IsStarProjection (f D.projection) := by
  refine ⟨adjointCoronaHom_apply V u, ?_⟩
  obtain ⟨D⟩ := exists_kazhdanData ↥L hL
  obtain ⟨f, hf, -⟩ :=
    maximalGroupCStar_existsUnique_lift_allUniverses ↥L
      ((adjointCoronaHom V).comp L.subtype)
  exact ⟨D, f, hf, isStarProjection_image D f⟩

/-- **`thm:compression-criterion`, sentence `3669402cc535`.**

> Property~(T) of `K` turns this into triviality in operator norm.

"This" is the preceding sentence's conclusion, Hilbert--Schmidt triviality on
the defect, that is `K ≤ R_{∞→2}(G)`.  The sentence asserts that property `(T)`
upgrades it to triviality of every corona homomorphism on `K`, which is the
closed proposition `NormalKazhdanRadical`.  The proof spent here is the printed
route of `NormalKazhdanPrintedRoute.lean` rather than the development's
moving-corner detector. -/
theorem manuscriptSentence_propertyTUpgradesHSTrivialityToOperatorNorm
    (G : Type) [Group G] [Countable G] (K : Subgroup G) [K.Normal]
    (hT : HasKazhdanPropertyT.{0, 0} ↥K)
    (hHS : K ≤ opToHSShadowResidual G) :
    K ≤ actualCoronaMFResidual G :=
  manuscriptNormalKazhdanRadical_printedRoute G K hT hHS

/-- **`thm:compression-criterion`, sentence `77affad8cafd`.**

> A corona homomorphism nontrivial on `K` compresses to a corner where the
> Kazhdan projection of `K` vanishes.

The corner is the complement `q = 1 - P` of the Kazhdan projection image.  The
four conjuncts are the four claims the sentence makes about it: `q` is a
projection; `q ≠ 0` exactly because the homomorphism is nontrivial on `K`;
`q` commutes with `ρ(G)`, so `q 𝓑 q` is a corner the homomorphism compresses
into; and `q P = 0`, which is "the Kazhdan projection of `K` vanishes" there.
The first and third are
`manuscriptSentence_coronaKazhdanComplementIsInvariantCorner`, the second is
`manuscriptSentence_complementNonzero` and the fourth is
`manuscriptSentence_complementIsCentralProjection`. -/
theorem manuscriptSentence_nontrivialCoronaHomCompressesToKillingCorner
    {G : Type} [Group G] (K : Subgroup G) [K.Normal]
    {B : Type} [CStarAlgebra B]
    (D : KazhdanData ↥K) (rho : G →* unitary B)
    (f : MaximalGroupCStar ↥K →⋆ₐ[ℂ] B)
    (hf : ∀ k : ↥K, f (maximalGroupCStarGenerator ↥K k) =
      ((rho (k : G) : unitary B) : B))
    {k0 : ↥K} (hk0 : rho (k0 : G) ≠ 1) :
    IsStarProjection ((1 : B) - f D.projection) ∧
      (1 : B) - f D.projection ≠ 0 ∧
      (∀ g : G, ((rho g : unitary B) : B) * ((1 : B) - f D.projection) =
        ((1 : B) - f D.projection) * ((rho g : unitary B) : B)) ∧
      ((1 : B) - f D.projection) * f D.projection = 0 := by
  obtain ⟨hproj, hcomm⟩ :=
    manuscriptSentence_coronaKazhdanComplementIsInvariantCorner K D rho f hf
  refine ⟨hproj, ?_, hcomm, ?_⟩
  · exact manuscriptSentence_complementNonzero D (rho.comp K.subtype) f hf hk0
  · exact (manuscriptSentence_complementIsCentralProjection
      (isSelfAdjoint_image D f) (image_mul_image D f)
      (fun _ : Empty ↦ (0 : B)) (fun i ↦ i.elim) (fun i ↦ i.elim)).2.1

/-- **`thm:compression-criterion`, sentence `72532c7673ac`.**

> On that corner, a group-algebra element within `1/4` of the Kazhdan
> projection has operator norm below `1/4`, while Hilbert--Schmidt triviality
> sends its normalized traces to the sum of its coefficients, which exceeds
> `3/4` (Theorem `thm:normal-kazhdan`).

The three conjuncts are the sentence's three clauses, at the printed data: the
combination exists by density of the group algebra, its corner norms have
`limsup` below `1/4`, its corner traces converge to the sum of its
coefficients, and that sum has modulus above `3/4`.  All four facts are proved
in `NormalKazhdanPrintedRoute.lean`; this declaration is the one place where
they appear as the single printed sentence.  The footnote of the sentence,
that a Hilbert--Schmidt bound on the multiplicative defect does not give an
operator-norm bound on the conjugation maps, is
`manuscriptFullRadicalsDoNotEntailNonsoficity` and is not restated here. -/
theorem manuscriptSentence_cornerNormBelowQuarterTraceAboveThreeQuarters
    {G : Type} [Group G] {L : Type} [Group L]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (KD : KazhdanData L)
    (f : MaximalGroupCStar L →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (iota : L →* G)
    (hf : ∀ s : L, f (maximalGroupCStarGenerator L s)
      = ((rho (iota s) : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)))
    (hres : ∀ s : L, iota s ∈ opToHSShadowResidual G)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (D : PrintedCornerData G (fun k ↦ X (φ k)))
    (hclass : ∀ g : G,
      normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ambientCornerSeq D g)
        = coronaRestrict X φ hφ
            ((1 - f KD.projection) *
              ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n)))) :
    ∃ (F : Finset L) (alpha : L → ℂ),
      Filter.limsup
          (fun k ↦ ‖∑ s ∈ F, alpha s •
            (D.cornerMap k (iota s) :
              Matrix (D.cornerModel k) (D.cornerModel k) ℂ)‖)
          Filter.cofinite < 1 / 4 ∧
        Filter.Tendsto
          (fun k ↦ normTrace (D.cornerModel k)
            (∑ s ∈ F, alpha s •
              (D.cornerMap k (iota s) :
                Matrix (D.cornerModel k) (D.cornerModel k) ℂ)))
          Filter.atTop (nhds (∑ s ∈ F, alpha s)) ∧
        (3 : ℝ) / 4 < ‖∑ s ∈ F, alpha s‖ := by
  obtain ⟨F, alpha, hclose, -, hbig⟩ :=
    manuscriptSentence_denseCombinationAndCharacter KD
  refine ⟨F, alpha, ?_, ?_, hbig⟩
  · exact manuscriptSentence_limsupCombinationLtQuarter X rho KD f iota hf
      φ hφ D hclass F alpha hclose
  · exact (manuscriptSentence_traceOfCombinationTendsTo iota hres D F alpha).2

/-! ## The "Kazhdan transport" setup paragraph -/

/-- **Kazhdan transport setup, sentence `fd2cafafd8fa`.**

> For an actual representation `ρ : G → U(d)` and `u ∈ G` with `uLu⁻¹ ≤ L`, the
> commutant `𝒞 = ρ(L)' ⊆ M_d(ℂ)` satisfies `ρ(u)* 𝒞 ρ(u) ⊆ 𝒞`, and the two
> spaces have the same finite dimension, so the inclusion is an equality; if
> `c` commutes with `L`, then `ρ(ucu⁻¹)` commutes with `ρ(L)`, and `ρ` is
> trivial on `𝔇_G(L)`.

Three conjuncts, one per clause.  `Manuscript/OneSidedMFRadical/FiniteDimensionalCommutant.lean`
owns the argument; the commutant is realized as the fixed submodule of the
adjoint representation on `End_k(V)`, and the printed "same finite dimension,
so the inclusion is an equality" is `fixedSubmodule_map_eq`, which is why the
conclusion is a map *equality* and not merely an inclusion.  Two departures
from the printed words, both weakenings of the hypothesis: the carrier asks
only for a finite-dimensional representation over a field, not for a unitary
one, and it is stated for `ρ : G →* (V ≃ₗ[k] V)`.  The last clause is
`compressionCentralizerDefect_le_ker` composed with
`printedDefect_le_compressionCentralizerDefect`, so it is stated for the
printed `𝔇_G(L)`. -/
theorem manuscriptSentence_exactRepresentationCommutantDimensionCount
    {G : Type u} {k : Type v} {V : Type w} [Group G] [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : G →* (V ≃ₗ[k] V)) (L : Subgroup G) (u : G)
    (hu : ∀ ell ∈ L, u * ell * u⁻¹ ∈ L) :
    (fixedSubmodule (adjointRep rho) L).map
        (adjointRep rho u : Module.End k (Module.End k V)) =
      fixedSubmodule (adjointRep rho) L ∧
      (∀ c : G, (∀ ell ∈ L, Commute c ell) → ∀ ell ∈ L,
        rho ⁅u * c * u⁻¹, ell⁆ = 1) ∧
      printedDefect L ≤ rho.ker := by
  obtain ⟨hmap, hdefect⟩ :=
    manuscriptFiniteDimensionalCommutantRigidity G k V rho L u hu
  exact ⟨hmap, hdefect,
    (printedDefect_le_compressionCentralizerDefect L).trans
      (compressionCentralizerDefect_le_ker rho L)⟩

/-- **Kazhdan transport setup, sentence `b1b62a9e3c06`.**

> An asymptotic representation has no exact commutant to count.

A negative remark, and the only formal content it has is the shape of the
printed replacement: `C₂(V, L)` is cut out by two *limit* conditions, a uniform
bound and a vanishing Hilbert--Schmidt displacement, and by no exact
commutation relation anywhere.  The declaration is therefore the unfolding of
`boundedHSCommutant`, true by `rfl`, and it is offered as a structural carrier
rather than as a theorem: the sentence has no mathematical claim of its own to
formalize. -/
theorem manuscriptSentence_asymptoticRepresentationHasNoExactCommutant
    {G : Type} [Group G] (B : OpAlmostRepresentation G) (L : Subgroup G)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) :
    x ∈ boundedHSCommutant B L ↔
      ((∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M) ∧
        ∀ ell : ↥L, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
          hsNormSq (B.model n)
              (x n - (B.map n (L.subtype ell) :
                    Matrix (B.model n) (B.model n) ℂ) * x n *
                  (B.map n (L.subtype ell) :
                    Matrix (B.model n) (B.model n) ℂ)ᴴ) ≤ ε) :=
  Iff.rfl

/-- **Kazhdan transport setup, sentence `240357aed76a`.**

> Property~(T) supplies a Kazhdan projection in its place, and stable
> finiteness of the corona replaces the dimension count.

Two conjuncts, one per clause: `exists_kazhdanData` is the first, and
`manuscriptNormMatrixCoronaStableFinite` is the second.  The sentence claims
only that the two replacements are available; the place where they are spent is
`thm:transport`'s own sentence `fbe5a19e1a8a`
(`manuscriptSentence_stableFinitenessGivesProjectionEquality`). -/
theorem manuscriptSentence_kazhdanProjectionAndStableFinitenessReplaceTheCount
    (L : Type) [Group L] (hL : HasKazhdanPropertyT.{0, 0} L) :
    Nonempty (KazhdanData L) ∧ NormMatrixCoronaStableFinite :=
  ⟨exists_kazhdanData L hL, manuscriptNormMatrixCoronaStableFinite⟩

/-! ## `cor:defect-hs`: the three sentences of the printed proof -/

/-- **The one new lemma of this module.**

`‖V_n(u) V_n(c) V_n(u)^* - V_n(ucu⁻¹)‖ → 0`: the conjugated microstate agrees
asymptotically, in operator norm, with the microstate of the conjugate.  This
is the estimate the printed proof of `cor:defect-hs` invokes with the words
"because `‖V_n(u)V_n(c)V_n(u)* - V_n(ucu⁻¹)‖ → 0`", and nothing in the tree
states it on its own: `Sofic/KazhdanCompressorCorner.lean` proves the same kind
of thing inline for the rotated corner (`conj_defect_vanishing`), against the
adjoint almost representation and for a compressed *generator*, not for a
conjugated centralizer element of the ambient group.

The three vanishing pieces are the two multiplicative defects `u · c` and
`(uc) · u⁻¹` and the inversion defect `V_n(u⁻¹) - V_n(u)^*`, each multiplied by
a contraction. -/
theorem conjugatedMap_opNormVanishing {G : Type} [Group G]
    (B : OpAlmostRepresentation G) (u c : G) :
    OpNormVanishing B (fun n ↦
      (B.map n u : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n c : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ -
          (B.map n (u * c * u⁻¹) : Matrix (B.model n) (B.model n) ℂ)) := by
  have hbound : ∀ (n : ℕ) (x : Matrix (B.model n) (B.model n) ℂ),
      x ∈ Matrix.unitaryGroup (B.model n) ℂ → ‖x‖ ≤ 1 := by
    intro n x hx
    letI : Nonempty (B.model n) := Fintype.card_pos_iff.mp (B.modelNonempty n)
    exact le_of_eq (CStarRing.norm_of_mem_unitary hx)
  have h1 : OpNormVanishing B (fun n ↦
      ((B.map n (u * c) : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n u : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n c : Matrix (B.model n) (B.model n) ℂ)) *
        (B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ) :=
    (multiplicativeDefect_vanishing B u c).mul_right_of_norm_le_one
      (fun n ↦ (B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ)
      (fun n ↦ hbound n _
        (conjTranspose_mem_unitaryGroup_of_mem (B.model n) (B.map n u).2))
  have h2 : OpNormVanishing B (fun n ↦
      (B.map n (u * c) : Matrix (B.model n) (B.model n) ℂ) *
        ((B.map n u⁻¹ : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ)) :=
    (map_inv_vanishing B u).mul_left_of_norm_le_one
      (fun n ↦ (B.map n (u * c) : Matrix (B.model n) (B.model n) ℂ))
      (fun n ↦ hbound n _ (B.map n (u * c)).2)
  have h3 : OpNormVanishing B (fun n ↦
      (B.map n (u * c * u⁻¹) : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n (u * c) : Matrix (B.model n) (B.model n) ℂ) *
          (B.map n u⁻¹ : Matrix (B.model n) (B.model n) ℂ)) :=
    multiplicativeDefect_vanishing B (u * c) u⁻¹
  refine (((h1.add h2).add h3).neg).congr fun n ↦ ?_
  noncomm_ring

/-- **`cor:defect-hs`, sentence `310f6df94cdf`.**

> Since `c` commutes with `L`, `(V_n(c)) ∈ 𝒞₂`, so
> `(V_n(u)V_n(c)V_n(u)*) ∈ 𝒞₂` by Theorem `thm:transport`, and then
> `(V_n(ucu⁻¹)) ∈ 𝒞₂` because `‖V_n(u)V_n(c)V_n(u)* - V_n(ucu⁻¹)‖ → 0`.

Three conjuncts, one per clause, at the printed `C₂(V, L)` -- the
Hilbert--Schmidt asymptotic commutant `boundedHSCommutant` of
`TransportCommutantEquality.lean`, not the old operator-norm object.  The first
clause is `centralizerSequence_mem_boundedHSCommutant`, the second is
`manuscriptOneSidedKazhdanTransportCommutantEquality` applied to it, and the
third is `IsAsymptoticCommutant.congr_hs` fed by `HSSqVanishing.of_opNormVanishing`
and the new `conjugatedMap_opNormVanishing` above.

The three memberships are proved at `boundedHSCommutant`, whose bound is the
operator norm, because that is where `thm:transport` is available as a set
equality.  The printed `C₂(V, L)` is now the Hilbert--Schmidt-bounded
`printedCTwo`, a *larger* set, so the fourth conjunct carries all three
memberships across `boundedHSCommutant_subset` and the sentence is matched at
the printed definition as well. -/
theorem manuscriptSentence_conjugatedCentralizerStaysInPrintedCommutant
    {G : Type} [Group G] (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (B : OpAlmostRepresentation G) (u : G) (hu : u ∈ compressionSet L)
    (c : G) (hc : ∀ ell ∈ L, Commute c ell) :
    (fun n ↦ (B.map n c : Matrix (B.model n) (B.model n) ℂ))
        ∈ boundedHSCommutant B L ∧
      adjointSequence B u
          (fun n ↦ (B.map n c : Matrix (B.model n) (B.model n) ℂ))
        ∈ boundedHSCommutant B L ∧
      (fun n ↦ (B.map n (u * c * u⁻¹) : Matrix (B.model n) (B.model n) ℂ))
        ∈ boundedHSCommutant B L ∧
      ((fun n ↦ (B.map n c : Matrix (B.model n) (B.model n) ℂ))
          ∈ printedCTwo B L ∧
        adjointSequence B u
            (fun n ↦ (B.map n c : Matrix (B.model n) (B.model n) ℂ))
          ∈ printedCTwo B L ∧
        (fun n ↦ (B.map n (u * c * u⁻¹) : Matrix (B.model n) (B.model n) ℂ))
          ∈ printedCTwo B L) := by
  have hcmem := centralizerSequence_mem_boundedHSCommutant B L c hc
  have heq := manuscriptOneSidedKazhdanTransportCommutantEquality G L hL B u hu
  have hadj : adjointSequence B u
      (fun n ↦ (B.map n c : Matrix (B.model n) (B.model n) ℂ))
        ∈ boundedHSCommutant B L := by
    have hmem := Set.mem_image_of_mem (adjointSequence B u) hcmem
    rwa [heq] at hmem
  have hconj : (fun n ↦
      (B.map n (u * c * u⁻¹) : Matrix (B.model n) (B.model n) ℂ))
        ∈ boundedHSCommutant B L := by
    refine ⟨⟨1, zero_le_one, fun n ↦ ?_⟩, ?_⟩
    · letI : Nonempty (B.model n) := Fintype.card_pos_iff.mp (B.modelNonempty n)
      exact (CStarRing.norm_of_mem_unitary (B.map n (u * c * u⁻¹)).2).le
    · refine IsAsymptoticCommutant.congr_hs hadj.2 ?_
      exact HSSqVanishing.of_opNormVanishing
        (conjugatedMap_opNormVanishing B u c)
  exact ⟨hcmem, hadj, hconj,
    boundedHSCommutant_subset B L hcmem,
    boundedHSCommutant_subset B L hadj,
    boundedHSCommutant_subset B L hconj⟩

/-- **`cor:defect-hs`, sentence `a6988bc68f49`.**

> So `‖V_n(ℓ)V_n(ucu⁻¹) - V_n(ucu⁻¹)V_n(ℓ)‖₂ → 0`, and by asymptotic
> multiplicativity `‖V_n([ucu⁻¹, ℓ]) - 1‖₂ → 0`.

Two conjuncts.  The first is the printed commutator form of the preceding
sentence's conclusion: membership in `C₂(V, L)` is stated with the conjugation
displacement `x - V x V*`, and right multiplication by the unitary `V_n(ℓ)`
turns it into the commutator without changing its Hilbert--Schmidt norm.  The
second is the printed display, already carried by
`manuscriptSentence_commutatorHilbertSchmidtVanishing`. -/
theorem manuscriptSentence_hsCommutatorVanishesAndDefectIsHSTrivial
    {G : Type} [Group G] (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (B : OpAlmostRepresentation G) (u : G) (hu : u ∈ compressionSet L)
    (c : G) (hc : ∀ ell ∈ L, Commute c ell)
    (ell : G) (hell : ell ∈ L) :
    HSSqVanishing B (fun n ↦
        (B.map n ell : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n (u * c * u⁻¹) : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n (u * c * u⁻¹) : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n ell : Matrix (B.model n) (B.model n) ℂ)) ∧
      Filter.Tendsto
        (fun n ↦ Real.sqrt (hsLengthSq (B.model n)
          ((B.map n ⁅u * c * u⁻¹, ell⁆ :
            Matrix (B.model n) (B.model n) ℂ))))
        Filter.atTop (nhds 0) := by
  refine ⟨?_, manuscriptSentence_commutatorHilbertSchmidtVanishing L hL u hu
    c hc ell hell B⟩
  have hd := (manuscriptSentence_conjugatedCentralizerStaysInPrintedCommutant
    L hL B u hu c hc).2.2.1.2 ⟨ell, hell⟩
  have hfactor : ∀ n : ℕ,
      (B.map n ell : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n (u * c * u⁻¹) : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n (u * c * u⁻¹) : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n ell : Matrix (B.model n) (B.model n) ℂ)
        = (-1 : ℂ) •
          (((B.map n (u * c * u⁻¹) : Matrix (B.model n) (B.model n) ℂ) -
              (B.map n ell : Matrix (B.model n) (B.model n) ℂ) *
                (B.map n (u * c * u⁻¹) :
                  Matrix (B.model n) (B.model n) ℂ) *
                (B.map n ell : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
            (B.map n ell : Matrix (B.model n) (B.model n) ℂ)) := by
    intro n
    have hV : (B.map n ell : Matrix (B.model n) (B.model n) ℂ)ᴴ *
        (B.map n ell : Matrix (B.model n) (B.model n) ℂ) = 1 := by
      have h := (B.map n ell).2
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
      exact h
    rw [neg_one_smul]
    noncomm_ring [hV]
  intro ε hε
  obtain ⟨N, hN⟩ := hd ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hgoal : hsNormSq (B.model n)
      ((B.map n ell : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n (u * c * u⁻¹) : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n (u * c * u⁻¹) : Matrix (B.model n) (B.model n) ℂ) *
            (B.map n ell : Matrix (B.model n) (B.model n) ℂ)) ≤ ε := by
    rw [hfactor n, hsNormSq_smul, hsNormSq_mul_right _ (B.map n ell).2]
    have hone : Complex.normSq (-1 : ℂ) = 1 := by simp
    rw [hone, one_mul]
    exact hN n hn
  exact hgoal

/-- **`cor:defect-hs`, sentence `acc79ac4eb5f`.**

> The elements with this property form a normal subgroup of `G`, so it contains
> `𝔇_G(L)`.

Three conjuncts: the shadow residual is a normal subgroup
(`opToHSShadowResidual_normal`), every printed defect generator has the
property, and therefore the whole printed defect `𝔇_G(L)` is contained in it.
The middle conjunct is what the printed "so" turns into the third: the printed
defect is by definition the normal closure of those generators, and a normal
subgroup containing the generators contains the closure. -/
theorem manuscriptSentence_hsTrivialElementsFormNormalSubgroupWithDefect
    {G : Type} [Group G] (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L) :
    (opToHSShadowResidual G).Normal ∧
      (∀ x ∈ printedDefectSet L, x ∈ opToHSShadowResidual G) ∧
      printedDefect L ≤ opToHSShadowResidual G := by
  have hle : printedDefect L ≤ opToHSShadowResidual G :=
    printedDefect_le_opToHSShadowResidual L hL
  exact ⟨opToHSShadowResidual_normal,
    fun x hx ↦ hle (Subgroup.subset_normalClosure hx), hle⟩

/-! ## "From Hilbert--Schmidt to operator norm": the setup sentence -/

/-- **"From Hilbert--Schmidt to operator norm", sentence `c9d3bf1f96b3`.**

> Restricting a corona homomorphism `ρ` to a corner requires a correction: a
> projection `q` commuting with `ρ(G)` has lifts `q_n` that commute only
> asymptotically with unitary lifts `U_n(g)` of `ρ(g)`, so the compressions
> `q_n U_n(g) q_n` are only approximately unitary in the matrix corners.

Three conjuncts, one per clause, stated at `PrintedCornerData`, the record of
`Analysis/PrintedCornerCompression.lean` that packages exactly the printed
data: genuine coordinate projections `q_n`, unitary lifts `U_n(g)`, and
asymptotic commutation.  The first conjunct is that asymptotic commutation.
The second is the quantitative form of "only approximately unitary": the Gram
defect of the compression is bounded by the *square* of the commutator norm.
The third is the correction itself: where the Gram defect is small, the polar
correction `cornerMap` is an honest unitary of the corner within twice that
defect of the compression. -/
theorem manuscriptSentence_cornerCompressionsAreOnlyApproximatelyUnitary
    {G : Type} [Group G] {model : ℕ → FiniteModel}
    (D : PrintedCornerData G model) (g : G) :
    Filter.Tendsto
        (fun n ↦ ‖(D.V n g : Matrix (model n) (model n) ℂ) * D.q n -
          D.q n * (D.V n g : Matrix (model n) (model n) ℂ)‖)
        Filter.atTop (nhds 0) ∧
      (∀ n : ℕ, ‖cornerGram (D.compress n g) - 1‖ ≤
        ‖(D.V n g : Matrix (model n) (model n) ℂ) * D.q n -
          D.q n * (D.V n g : Matrix (model n) (model n) ℂ)‖ ^ 2) ∧
      (∀ n : ℕ, ‖cornerGram (D.compress n g) - 1‖ ≤ (1 / 2 : ℝ) →
        ‖(D.cornerMap n g :
              Matrix (D.cornerModel n) (D.cornerModel n) ℂ) -
            D.compress n g‖
          ≤ 2 * ‖cornerGram (D.compress n g) - 1‖) :=
  ⟨D.commutator_vanishing g,
    fun n ↦ D.norm_cornerGram_compress_le n g,
    fun _ h ↦ D.norm_cornerMap_sub_compress_le h⟩

end

end CompressionCriterionSentences
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation
open Manuscript.OneSidedMFRadical.CompressionCriterionSentences

#audit_axioms manuscriptSentence_adIsAsymptoticallyMultiplicativeUnitaryFamily
#audit_axioms manuscriptSentence_adIsTwoLipschitz
#audit_axioms manuscriptSentence_adClassesFormCoronaHomomorphism
#audit_axioms manuscriptSentence_compressorClassAndKazhdanProjectionImage
#audit_axioms manuscriptSentence_propertyTUpgradesHSTrivialityToOperatorNorm
#audit_axioms manuscriptSentence_nontrivialCoronaHomCompressesToKillingCorner
#audit_axioms manuscriptSentence_cornerNormBelowQuarterTraceAboveThreeQuarters
#audit_axioms manuscriptSentence_exactRepresentationCommutantDimensionCount
#audit_axioms manuscriptSentence_asymptoticRepresentationHasNoExactCommutant
#audit_axioms manuscriptSentence_kazhdanProjectionAndStableFinitenessReplaceTheCount
#audit_axioms conjugatedMap_opNormVanishing
#audit_axioms manuscriptSentence_conjugatedCentralizerStaysInPrintedCommutant
#audit_axioms manuscriptSentence_hsCommutatorVanishesAndDefectIsHSTrivial
#audit_axioms manuscriptSentence_hsTrivialElementsFormNormalSubgroupWithDefect
#audit_axioms manuscriptSentence_cornerCompressionsAreOnlyApproximatelyUnitary
