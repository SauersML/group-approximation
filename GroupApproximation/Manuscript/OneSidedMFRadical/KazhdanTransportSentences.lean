import GroupApproximation.Analysis.FiniteCStarMurrayVonNeumann
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanProjectionOrderLiteral
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefectShadow
import GroupApproximation.Manuscript.OneSidedMFRadical.ShadowResidual
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Sofic.UltraproductAdjointAmbient
import GroupApproximation.Sofic.KazhdanCornerMatrices

/-!
# Proof sentences of the compression criterion, the projection order, the
transport theorem and the Hilbert--Schmidt defect corollary

`non_mf_groups_exist.tex`.  One declaration per printed sentence, for the
sentences of

* the paragraph following `thm:compression-criterion`,
* the proof of `lem:kazhdan-projection-order`,
* the proof of `thm:transport`,
* the proof of `cor:defect-hs`.

Every statement is the printed sentence and nothing more, and each proof
follows the printed dependency graph.  The four theorems these sentences serve
are already carried by `PrintedCriterion`, `KazhdanProjectionOrderLiteral`,
`KazhdanTransport`/`TransportCommutantEquality` and `DefectHS`; what is new
here is the intermediate step of each printed proof, named on its own.

The manuscript's ambient `𝓑 = ∏_n B(M_{d_n}(ℂ)) / ⊕_n B(M_{d_n}(ℂ))` is the
repository's `NormMatrixCStarCorona` on the doubled models, and the printed
`σ̃(g) = [Ad V_n(g)]` is `adjointCoronaHom`: after choosing matrix units the
conjugation `ξ ↦ U ξ U*` is the matrix `conjDouble U` on the index type
`Y × Y`, which is the manuscript's "coordinate sizes `d_n²`".
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open MaximalCStarKazhdanProjection
open scoped Matrix.Norms.L2Operator commutatorElement

noncomputable section

universe u v w

/-! ## `thm:compression-criterion`: the four sentences after the statement -/

/-- **`thm:compression-criterion`, sentence `e69d0bca295c`.**

> Every operator norm asymptotic representation is asymptotically trivial on
> `𝔇_G(L)` in normalized Hilbert--Schmidt norm: `𝔇_G(L) ≤ R_{∞→2}(G)`.

The displayed inclusion is the first conjunct; the sentence's own words — that
*every* operator-norm asymptotic representation sends *every* element of the
printed defect to the identity in normalized Hilbert--Schmidt norm — are the
second, in the ordinary sequential sense `‖V_n(x) - 1‖₂ → 0`. -/
theorem manuscriptSentence_defectAsymptoticallyTrivialInHS
    {G : Type} [Group G] (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L) :
    printedDefect L ≤ opToHSShadowResidual G ∧
      ∀ (V : OpAlmostRepresentation G), ∀ x ∈ printedDefect L,
        Tendsto
          (fun n ↦ Real.sqrt (hsLengthSq (V.model n)
            ((V.map n x : Matrix (V.model n) (V.model n) ℂ))))
          atTop (nhds 0) := by
  have hle : printedDefect L ≤ opToHSShadowResidual G :=
    printedDefect_le_opToHSShadowResidual_direct L hL
  refine ⟨hle, ?_⟩
  intro V x hx
  have hker : x ∈ hsKernel V :=
    (mem_opToHSShadowResidual_iff_forall_hsKernel x).mp (hle hx) V
  exact (isHSNull_iff_tendsto V x).mp ((mem_hsKernel_iff V x).mp hker)

/-- **`thm:compression-criterion`, sentence `b60868d52039`.**

> For a corona representation, the complement of the Kazhdan projection is a
> `G`-invariant corner.

`P = f p` is the image of the Kazhdan projection of `C*_max(K)` under the
extension of `ρ|_K`, and `q = 1 - P`.  "`G`-invariant corner" is the
conjunction of the two printed clauses: `q` is a projection, and `q` commutes
with `ρ(G)`, so `q 𝓑 q` is carried onto itself by conjugation by every `ρ(g)`.
Normality of `K` is what supplies the commutation: it makes the one-sided
inclusion `U π(K) U* ⊆ π(K)` of `lem:kazhdan-projection-order` available for
`U = ρ(g)` *and* for `U = ρ(g)*`, and the two absorption identities together
force `ρ(g)* P ρ(g) = P`. -/
theorem manuscriptSentence_coronaKazhdanComplementIsInvariantCorner
    {G : Type} [Group G] (K : Subgroup G) [K.Normal]
    {B : Type v} [CStarAlgebra B]
    (D : KazhdanData ↥K) (rho : G →* unitary B)
    (f : MaximalGroupCStar ↥K →⋆ₐ[ℂ] B)
    (hf : ∀ k : ↥K, f (maximalGroupCStarGenerator (↥K) k) =
      ((rho (k : G) : unitary B) : B)) :
    IsStarProjection (1 - f D.projection) ∧
      ∀ g : G,
        ((rho g : unitary B) : B) * (1 - f D.projection) =
          (1 - f D.projection) * ((rho g : unitary B) : B) := by
  have hPproj : IsStarProjection (f D.projection) := isStarProjection_image D f
  have hstar : ∀ g : G,
      star ((rho g : unitary B) : B) = ((rho g⁻¹ : unitary B) : B) := by
    intro g
    rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
  have hfpi : ∀ k : ↥K, f (maximalGroupCStarGenerator (↥K) k) =
      (((rho.comp K.subtype) k : unitary B) : B) := hf
  have hcompAll : ∀ g : G, ∀ k : ↥K, ∃ k' : ↥K,
      ((rho g : unitary B) : B) *
            (((rho.comp K.subtype) k : unitary B) : B) *
            star ((rho g : unitary B) : B)
        = (((rho.comp K.subtype) k' : unitary B) : B) := by
    intro g k
    refine ⟨⟨g * (k : G) * g⁻¹,
      (inferInstance : K.Normal).conj_mem (k : G) k.2 g⟩, ?_⟩
    have hmap : rho (g * (k : G) * g⁻¹)
        = rho g * rho (k : G) * rho g⁻¹ := by
      rw [map_mul, map_mul]
    show ((rho g : unitary B) : B) * ((rho (k : G) : unitary B) : B) *
        star ((rho g : unitary B) : B)
      = ((rho (g * (k : G) * g⁻¹) : unitary B) : B)
    rw [hstar g]
    exact (congrArg Subtype.val hmap).symm
  have hkey : ∀ g : G,
      star ((rho g : unitary B) : B) * f D.projection *
          ((rho g : unitary B) : B)
        = f D.projection := by
    intro g
    have h2 := star_conj_image_mul_image D (rho.comp K.subtype) f hfpi
      ((rho g : unitary B) : B) (rho g).property.1 (rho g).property.2
      (hcompAll g)
    have h3 := conj_image_mul_image D (rho.comp K.subtype) f hfpi
      ((rho g⁻¹ : unitary B) : B) (rho g⁻¹).property.1 (rho g⁻¹).property.2
      (hcompAll g⁻¹)
    have hginv : star ((rho g⁻¹ : unitary B) : B)
        = ((rho g : unitary B) : B) := by
      rw [hstar g⁻¹, inv_inv]
    rw [hginv, ← hstar g] at h3
    exact h2.symm.trans h3
  have hcommute : ∀ g : G,
      ((rho g : unitary B) : B) * f D.projection
        = f D.projection * ((rho g : unitary B) : B) := by
    intro g
    have hLHS : ((rho g : unitary B) : B) *
        (star ((rho g : unitary B) : B) * f D.projection *
          ((rho g : unitary B) : B))
        = f D.projection * ((rho g : unitary B) : B) := by
      calc ((rho g : unitary B) : B) *
            (star ((rho g : unitary B) : B) * f D.projection *
              ((rho g : unitary B) : B))
          = (((rho g : unitary B) : B) * star ((rho g : unitary B) : B)) *
              f D.projection * ((rho g : unitary B) : B) := by noncomm_ring
        _ = f D.projection * ((rho g : unitary B) : B) := by
            rw [(rho g).property.2, one_mul]
    rw [hkey g] at hLHS
    exact hLHS
  have hq : IsStarProjection (1 - f D.projection) := by
    constructor
    · show (1 - f D.projection) * (1 - f D.projection) = 1 - f D.projection
      rw [sub_mul, one_mul, mul_sub, mul_one, hPproj.isIdempotentElem.eq,
        sub_self, sub_zero]
    · show star (1 - f D.projection) = 1 - f D.projection
      rw [star_sub, star_one, hPproj.isSelfAdjoint.star_eq]
  refine ⟨hq, fun g ↦ ?_⟩
  rw [mul_sub, sub_mul, mul_one, one_mul, hcommute g]

/-- **`thm:compression-criterion`, sentence `0418dd5f3a67`.**

> The Kazhdan inequality forces this corner to vanish when `K ≤ 𝔇_G(L)`.

With `K ≤ 𝔇_G(L)` the criterion's own conclusion puts `K` inside the MF
radical, so every corona homomorphism trivialises `K`; the image of the
Kazhdan projection of `C*_max(K)` under a trivialising extension is `1`, and
the corner `q = 1 - P` is therefore `0`. -/
theorem manuscriptSentence_kazhdanInequalityKillsCornerOnDefect
    {G : Type} [Group G] [Countable G] (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (K : Subgroup G) [K.Normal] (hK : HasKazhdanPropertyT.{0, 0} ↥K)
    (hKD : K ≤ printedDefect L)
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (hX : ∀ n, 0 < Fintype.card (X n))
    (D : KazhdanData ↥K)
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (f : MaximalGroupCStar ↥K →⋆ₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ X n))
    (hf : ∀ k : ↥K, f (maximalGroupCStarGenerator (↥K) k) =
      ((rho (k : G) :
          unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n))) :
    (1 : NormMatrixCStarCorona (fun n ↦ X n)) - f D.projection = 0 := by
  have hres : K ≤ actualCoronaMFResidual G :=
    normalKazhdan_le_actualCoronaMFResidual_of_le_printedDefect L hL K hK hKD
  have hkill : ∀ k : ↥K, f (maximalGroupCStarGenerator (↥K) k) = 1 := by
    intro k
    have hrho : rho (k : G) = 1 :=
      (mem_actualCoronaMFResidual_iff).mp (hres k.2) X hX rho
    rw [hf k]
    exact congrArg Subtype.val hrho
  have hone : f D.projection = 1 := image_projection_eq_one D f hkill
  simp [hone]

/-- **`thm:compression-criterion`, sentence `b65f5b8e036b`.**

> Many Kazhdan groups are residually finite and so MF.

The printed implication, with the property-`(T)` hypothesis carried but unused
— which is the sentence's point: residual finiteness, not property `(T)`, is
what produces the matrix models.  `IsCDEOperatorMF` is the literal
Carrión--Dadarlat--Eckhardt predicate. -/
theorem manuscriptSentence_residuallyFiniteKazhdanGroupsAreMF
    (K : Type) [Group K] [Countable K] [Group.ResiduallyFinite K]
    (_hT : HasKazhdanPropertyT.{0, 0} K) :
    IsCDEOperatorMF K :=
  (isCDEOperatorMF_iff_isOperatorMF K).mpr isOperatorMF_of_residuallyFinite

/-! ## `lem:kazhdan-projection-order`: the closing sentence of the proof -/

/-- **`lem:kazhdan-projection-order`, sentence `cbe17a5c126c`.**

> So `U* Fix π(L) ⊆ Fix π(L)`, so the range projection `U* P U` is dominated
> by `P` in `B(H)`.

`P` is the orthogonal projection onto `Fix π(L)`, which is what `hPfix`
records, and `hPidem` is idempotence of a projection.  The first conjunct is
the printed inclusion `U* Fix π(L) ⊆ Fix π(L)`; the second is the printed
domination, read as the inclusion of ranges it abbreviates: every vector in
the range of `U* P U` already lies in the range of `P`. -/
theorem manuscriptSentence_movedFixedSpaceInclusionAndProjectionOrder
    {L : Type u} [Group L] {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (pi : L →* unitary (E →L[ℂ] E)) (U : unitary (E →L[ℂ] E))
    (hcomp : ∀ l : L, ∃ l' : L,
      ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E) *
            ((pi l : unitary (E →L[ℂ] E)) : E →L[ℂ] E) *
            star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        = ((pi l' : unitary (E →L[ℂ] E)) : E →L[ℂ] E))
    (P : E →L[ℂ] E) (hPidem : P * P = P)
    (hPfix : ∀ x : E, P x = x ↔
      ∀ l : L, ((pi l : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x) :
    (∀ x : E, (∀ l : L, ((pi l : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x) →
        ∀ l : L, ((pi l : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
            ((star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) x)
          = (star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) x) ∧
      ∀ x : E,
        P ((star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E))
              (P (((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x)))
          = (star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E))
              (P (((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x)) := by
  have hpart1 : ∀ x : E,
      (∀ l : L, ((pi l : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x) →
        ∀ l : L, ((pi l : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
            ((star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) x)
          = (star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) x := by
    intro x hx l
    obtain ⟨l', hl'⟩ := hcomp l
    have hmul : ((pi l : unitary (E →L[ℂ] E)) : E →L[ℂ] E) *
          star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        = star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E) *
          ((pi l' : unitary (E →L[ℂ] E)) : E →L[ℂ] E) := by
      rw [← hl']
      calc ((pi l : unitary (E →L[ℂ] E)) : E →L[ℂ] E) *
            star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
          = (star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E) *
              ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) *
              ((pi l : unitary (E →L[ℂ] E)) : E →L[ℂ] E) *
              star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E) := by
            rw [U.property.1, one_mul]
        _ = star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E) *
              (((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E) *
                ((pi l : unitary (E →L[ℂ] E)) : E →L[ℂ] E) *
                star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) := by
            noncomm_ring
    have happ : ((pi l : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
          ((star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) x)
        = (star ((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E))
          (((pi l' : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x) :=
      congrArg (fun T : E →L[ℂ] E ↦ T x) hmul
    rw [happ, hx l']
  refine ⟨hpart1, ?_⟩
  intro x
  have hy : P (P (((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x))
      = P (((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x) :=
    congrArg (fun T : E →L[ℂ] E ↦
      T (((U : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x)) hPidem
  exact (hPfix _).mpr (hpart1 _ ((hPfix _).mp hy))

/-! ## `thm:transport`: the sentences of the printed proof -/

/-- **`thm:transport`, sentence `dc5b8bea1700`.**

> …so the conjugation actions are multiplicative modulo `c₀` because the
> multiplicative defects of `(V_n)` tend to zero in operator norm.

The first conjunct is the printed estimate `‖Ad(A) - Ad(B)‖ ≤ 2‖A - B‖`, with
`Ad(A)` written in the row-major matrix units of `M_{d_n}(ℂ)` as
`conjDouble A`; the second is its printed consequence — the multiplicative
defects of the conjugation actions vanish in operator norm, which is exactly
membership of the defect sequence in `c₀`. -/
theorem manuscriptSentence_conjugationActionsMultiplicativeModC0
    {G : Type} [Group G] (V : OpAlmostRepresentation G) :
    (∀ (n : ℕ) (A C : Matrix (V.model n) (V.model n) ℂ),
        A ∈ Matrix.unitaryGroup (V.model n) ℂ →
        C ∈ Matrix.unitaryGroup (V.model n) ℂ →
        ‖conjDouble A - conjDouble C‖ ≤ 2 * ‖A - C‖) ∧
      ∀ g h : G, KazhdanCornerMatrices.OpNormVanishing V.adjoint (fun n ↦
        (V.adjoint.map n (g * h) :
            Matrix (V.adjoint.model n) (V.adjoint.model n) ℂ) -
          (V.adjoint.map n g :
              Matrix (V.adjoint.model n) (V.adjoint.model n) ℂ) *
            (V.adjoint.map n h :
              Matrix (V.adjoint.model n) (V.adjoint.model n) ℂ)) :=
  ⟨fun _ _ _ hA hC ↦ l2_opNorm_conjDouble_sub_le_two hA hC,
    fun g h ↦ KazhdanCornerMatrices.multiplicativeDefect_vanishing V.adjoint g h⟩

/-- **`thm:transport`, sentence `354d89cc595c`.**

> By the preceding estimate, `g ↦ σ̃(g)` is a homomorphism `G → U(𝓑)`.

`σ̃(g)` is the class of the coordinate operators `Ad(V_n(g))` in the norm
matrix corona `𝓑`; the first conjunct records that reading, and the remaining
two are the homomorphism property.  The "preceding estimate" enters as the
vanishing of the multiplicative defect of the conjugation actions, which is
what puts the coordinate defect in the ideal that is quotiented out. -/
theorem manuscriptSentence_sigmaTildeIsHomomorphism
    {G : Type} [Group G] (V : OpAlmostRepresentation G)
    [∀ n, Nonempty (V.adjoint.model n)] :
    (∀ g : G, adjointCoronaHom V g =
        unitarySequenceToCorona V.adjoint.model
          (fun n ↦ V.adjoint.map n g)) ∧
      (∀ g h : G, adjointCoronaHom V (g * h)
          = adjointCoronaHom V g * adjointCoronaHom V h) ∧
        adjointCoronaHom V 1 = 1 :=
  ⟨fun g ↦ adjointCoronaHom_apply V g,
    fun g h ↦ map_mul (adjointCoronaHom V) g h,
    map_one (adjointCoronaHom V)⟩

/-- **`thm:transport`, sentence `917c4e8a8b2b`.**

> So its restriction to `L` extends to a `*`-homomorphism `C*_max(L) → 𝓑`.

The restriction of `σ̃` to `L` is `σ̃ ∘ ι_L`, and the extension is the unique
`⋆`-homomorphism out of `C*_max(L)` carrying each canonical unitary of `L` to
its `σ̃`-image.  Uniqueness is part of the printed definite article. -/
theorem manuscriptSentence_restrictionExtendsToMaximalCStar
    {G : Type} [Group G] (L : Subgroup G) (V : OpAlmostRepresentation G)
    [∀ n, Nonempty (V.adjoint.model n)] :
    ∃! f : MaximalGroupCStar ↥L →⋆ₐ[ℂ]
        NormMatrixCStarCorona (fun n ↦ V.adjoint.model n),
      ∀ l : ↥L, f (maximalGroupCStarGenerator (↥L) l) =
        ((adjointCoronaHom V (l : G) :
            unitary (NormMatrixCStarCorona (fun n ↦ V.adjoint.model n))) :
          NormMatrixCStarCorona (fun n ↦ V.adjoint.model n)) :=
  maximalGroupCStar_existsUnique_lift_allUniverses ↥L
    ((adjointCoronaHom V).comp L.subtype)

/-- **`thm:transport`, sentence `98d7681d0af2`.**

> Since `uLu⁻¹ ≤ L`, the unitary `U = σ̃(u)` satisfies the hypothesis of
> Lemma~`lem:kazhdan-projection-order`, and so `U* P U ≤ P` inside `𝓑`.

The first conjunct is the hypothesis of `lem:kazhdan-projection-order`
verified for `U = σ̃(u)`; the second is the conclusion of that lemma in the
printed Loewner order, which for a `C*`-algebra carrying no order hypothesis
is its own spectral order — the reading fixed by
`KazhdanProjectionOrderLiteral`.  `P = f p` is the image of the Kazhdan
projection of `C*_max(L)` under the extension of the previous sentence. -/
theorem manuscriptSentence_compressorSatisfiesProjectionOrder
    {G : Type} [Group G] (L : Subgroup G) (u : G)
    (hu : ∀ l ∈ L, u * l * u⁻¹ ∈ L)
    {B : Type v} [CStarAlgebra B] (sigma : G →* unitary B)
    (D : KazhdanData ↥L)
    (f : MaximalGroupCStar ↥L →⋆ₐ[ℂ] B)
    (hf : ∀ l : ↥L, f (maximalGroupCStarGenerator (↥L) l) =
      ((sigma (l : G) : unitary B) : B)) :
    letI : PartialOrder B := CStarAlgebra.spectralOrder B
    (∀ l : ↥L, ∃ l' : ↥L,
        ((sigma u : unitary B) : B) * ((sigma (l : G) : unitary B) : B) *
            star ((sigma u : unitary B) : B)
          = ((sigma (l' : G) : unitary B) : B)) ∧
      star ((sigma u : unitary B) : B) * f D.projection *
          ((sigma u : unitary B) : B)
        ≤ f D.projection := by
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hstar : star ((sigma u : unitary B) : B)
      = ((sigma u⁻¹ : unitary B) : B) := by
    rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
  have hfpi : ∀ l : ↥L, f (maximalGroupCStarGenerator (↥L) l) =
      (((sigma.comp L.subtype) l : unitary B) : B) := hf
  have hcomp : ∀ l : ↥L, ∃ l' : ↥L,
      ((sigma u : unitary B) : B) *
            (((sigma.comp L.subtype) l : unitary B) : B) *
            star ((sigma u : unitary B) : B)
        = (((sigma.comp L.subtype) l' : unitary B) : B) := by
    intro l
    refine ⟨⟨u * (l : G) * u⁻¹, hu (l : G) l.2⟩, ?_⟩
    have hmap : sigma (u * (l : G) * u⁻¹)
        = sigma u * sigma (l : G) * sigma u⁻¹ := by
      rw [map_mul, map_mul]
    show ((sigma u : unitary B) : B) * ((sigma (l : G) : unitary B) : B) *
        star ((sigma u : unitary B) : B)
      = ((sigma (u * (l : G) * u⁻¹) : unitary B) : B)
    rw [hstar]
    exact (congrArg Subtype.val hmap).symm
  refine ⟨?_, ?_⟩
  · exact fun l ↦ hcomp l
  · exact star_conj_image_le D (sigma.comp L.subtype) f hfpi
      ((sigma u : unitary B) : B) (sigma u).property.1 (sigma u).property.2
      hcomp

/-- **`thm:transport`, sentence `fbe5a19e1a8a`.**

> Lemma~`lem:stable-finite` then gives `U* P U = P`: `U` commutes with `P`,
> and both `Uξ` and `U*ξ` are fixed by `σ(L)`.

`horder` is the printed `U* P U ≤ P` of the previous sentence in its
absorption form, and Dedekind finiteness is what `lem:stable-finite` supplies
for the norm matrix corona
(`normMatrixCStarCorona_isDedekindFiniteMonoid`).  The three printed
consequences are the three conjuncts, in the printed order; `hfix` records
that the range of the represented `P` is `Fix σ(L)`, which is the property of
the Kazhdan projection used to read the third one. -/
theorem manuscriptSentence_stableFinitenessGivesProjectionEquality
    {B : Type v} [CStarAlgebra B] [IsDedekindFiniteMonoid B]
    {P U : B} (hP : IsStarProjection P)
    (_hU : star U * U = 1) (hU' : U * star U = 1)
    (horder : (star U * P * U) * P = star U * P * U)
    {L : Type u} [Group L] (sigma : L →* unitary B)
    {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (rep : B →⋆ₐ[ℂ] (E →L[ℂ] E))
    (hfix : ∀ x : E, rep P x = x ↔
      ∀ l : L, rep ((sigma l : unitary B) : B) x = x) :
    star U * P * U = P ∧ U * P = P * U ∧
      ∀ x : E, (∀ l : L, rep ((sigma l : unitary B) : B) x = x) →
        (∀ l : L, rep ((sigma l : unitary B) : B) (rep U x) = rep U x) ∧
          (∀ l : L, rep ((sigma l : unitary B) : B) (rep (star U) x)
            = rep (star U) x) := by
  have hQ : IsStarProjection (star U * P * U) := by
    have h := isStarProjection_isometry_conjugate (p := P) (u := star U) hP
      (by rwa [star_star])
    rwa [star_star] at h
  have hPQ : P * (star U * P * U) = star U * P * U := by
    have h := congrArg star horder
    rw [star_mul, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq] at h
    exact h
  have hmvn : MurrayVonNeumannEquiv (star U * P * U) P := by
    have h := MurrayVonNeumannEquiv.of_isometry_conjugate (p := P)
      (u := star U) hP (by rwa [star_star])
    rw [star_star] at h
    exact h.symm
  have heq : star U * P * U = P :=
    dedekindFiniteCStar_eq_of_murrayVonNeumannEquiv_of_absorbs hQ hP hPQ hmvn
  have hcommute : U * P = P * U := by
    have h : U * (star U * P * U) = U * P :=
      congrArg (fun z : B ↦ U * z) heq
    have hleft : U * (star U * P * U) = P * U := by
      calc U * (star U * P * U) = (U * star U) * P * U := by noncomm_ring
        _ = P * U := by rw [hU', one_mul]
    rw [hleft] at h
    exact h.symm
  have hcommute' : star U * P = P * star U := by
    have h := congrArg star hcommute
    rw [star_mul, star_mul, hP.isSelfAdjoint.star_eq] at h
    exact h.symm
  refine ⟨heq, hcommute, ?_⟩
  intro x hx
  have hPx : rep P x = x := (hfix x).mpr hx
  have hfixU : rep P (rep U x) = rep U x := by
    have h : rep P * rep U = rep U * rep P := by
      rw [← map_mul rep P U, ← map_mul rep U P, hcommute]
    have happ : rep P (rep U x) = rep U (rep P x) :=
      congrArg (fun T : E →L[ℂ] E ↦ T x) h
    rw [happ, hPx]
  have hfixUstar : rep P (rep (star U) x) = rep (star U) x := by
    have h : rep P * rep (star U) = rep (star U) * rep P := by
      rw [← map_mul rep P (star U), ← map_mul rep (star U) P, hcommute']
    have happ : rep P (rep (star U) x) = rep (star U) (rep P x) :=
      congrArg (fun T : E →L[ℂ] E ↦ T x) h
    rw [happ, hPx]
  exact ⟨(hfix _).mp hfixU, (hfix _).mp hfixUstar⟩

/-! ## `cor:defect-hs`: the closing display of the printed proof -/

/-- **`cor:defect-hs`, sentence `fb1df1a24e3f`.**

> So `‖V_n([ucu⁻¹, ℓ]) - 1‖₂ → 0`  (`ℓ ∈ L`).

The printed display, for an arbitrary operator norm asymptotic representation
`(V_n)`: the normalized Hilbert--Schmidt displacement of the represented
compression commutator from the identity converges to zero along the full
sequence.  Intersecting over `(V_n)` is the next printed sentence and is
`manuscriptCompressionDefectHSInvisible`. -/
theorem manuscriptSentence_commutatorHilbertSchmidtVanishing
    {G : Type} [Group G] (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (u : G) (hu : ∀ l ∈ L, u * l * u⁻¹ ∈ L)
    (c : G) (hc : ∀ l ∈ L, Commute c l)
    (ell : G) (hell : ell ∈ L)
    (V : OpAlmostRepresentation G) :
    Tendsto
      (fun n ↦ Real.sqrt (hsLengthSq (V.model n)
        ((V.map n ⁅u * c * u⁻¹, ell⁆ :
          Matrix (V.model n) (V.model n) ℂ))))
      atTop (nhds 0) := by
  have hmem : ⁅u * c * u⁻¹, ell⁆ ∈ opToHSShadowResidual G :=
    manuscriptCompressionDefectHSInvisible G L hL u hu c hc ell hell
  exact (isHSNull_iff_tendsto V _).mp
    ((mem_hsKernel_iff V _).mp
      ((mem_opToHSShadowResidual_iff_forall_hsKernel _).mp hmem V))

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
