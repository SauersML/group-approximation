import GroupApproximation.Sofic.MFDefinitions
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Analysis.MFAlgebraDimensionNormalization
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefinitions
import GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoints
import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarConsequence
import GroupApproximation.Computability.MFRecognitionPi02
import GroupApproximation.Computability.MFRecognitionImpossible
import GroupApproximation.Computability.SecondLevelIndexSets
import GroupApproximation.Manuscript.MFRecognition.RecognitionMainTheorem
import GroupApproximation.Manuscript.MFRecognition.TensorSynchronization

/-!
# `mf_recognition_complexity.tex`: abstract, `sec:prelim`, and the `sec:hnn`
introduction, sentence by sentence

Lane `p2-prelim-sentences`. One declaration per printed sentence that asserts
something: definitions get a `def`/`abbrev` with the printed name and
assertions get theorems, stated literally and proved from existing modules
per `RULES.md`. Sentences that are pure literature attribution or naming
remarks with no separate checkable mathematical content (`297f1fbfa1f5`,
`d7be1aaf4514`, `2a0d28e65002`, `1324ce0327e8`, `8fcb4c37d063`, `a45ab71d52c5`)
are not given a Lean declaration; each is noted at its place below.

Covered ranges:
* abstract (tex lines 78-98): `aea2e8dcb3b4`, `bae33ce50d1a`, `c54ed6a64a49`,
  `4ee80496e936`, `675d05a8d993`, `31e75269416c`.
* `sec:prelim`, "MF groups" (tex lines 197-235): `a7c657eb85c7`+`6201111b83a0`,
  `297f1fbfa1f5` (skipped), `d7be1aaf4514` (skipped), `2a0d28e65002` (skipped),
  `05203f9f8c7f`+`bf4989940236`, `089abd2aa0ca`, `3a88dbf43438`,
  `76bc4eff61a4`, `24a9424a74f6`.
* `sec:hnn` introduction (tex lines 358-388): `1324ce0327e8` (skipped),
  `47604663f047`, `8fcb4c37d063` (skipped), `a45ab71d52c5` (skipped),
  `2d35e11ad64d`, `b89e22ba5034`, `96784974461f`.
  (`49af36bf9b2e`, the corner-embedding remark, is proved separately in
  `CoronaEmbeddingRemark.lean`, landed on main.)

`47604663f047` (`thm:hnn-permanence`'s headline) is stated with
`TensorSynchronization.HNNPermanenceInputs` as its leading hypothesis rather
than against the `hnn-permanence` lane's own module directly: that module is
not yet on `main`, while `HNNPermanenceInputs` (landed, in
`TensorSynchronization.lean`) already carries exactly its two printed
ingredients as fields, in the `HullInputs` idiom.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Preliminaries

open PresentationCodes ArithmeticalHierarchy
open GroupApproximation.Manuscript.OneSidedMFRadical
open GroupApproximation.Manuscript.MFRecognition.Recognition
open GroupApproximation.Manuscript.MFRecognition.TensorSynchronization

/-! ## Abstract -/

/-- Sentence `aea2e8dcb3b4`: "A countable group is MF if it admits
finite-dimensional unitary models that are asymptotically multiplicative and
asymptotically separate nonidentity elements in operator norm."

Formalized through the development's bundled all-pairs-separation data
`WeakMFApproximation` (asymptotic multiplicativity plus a fixed positive
separation constant, eventually attained between every pair of distinct
elements), which is what the existing biconditional
`isCDEOperatorMF_iff_nonempty_weakMFApproximation` characterizes exactly.
The printed nonidentity-only separation clause is the special case of the
forward direction recorded, with the same honest caveat about the missing
converse, by `isCDEOperatorMF_exists_separating_unitary_models`. -/
theorem isOperatorMF_iff_nonempty_weakMFApproximation
    (G : Type) [Group G] [Countable G] :
    IsOperatorMF G ↔ Nonempty (WeakMFApproximation G) :=
  (isCDEOperatorMF_iff_isOperatorMF G).symm.trans
    (isCDEOperatorMF_iff_nonempty_weakMFApproximation G)

/-- Sentence `bae33ce50d1a`: "We show that deciding whether a finite
presentation defines an MF group is `Π⁰₂`-complete."

The `Π⁰₂` upper bound is `MFRecognitionPi02.operatorMFCode_pi02`
(unconditional); completeness additionally needs `Π⁰₂`-hardness, which needs
the finite-presentation compiler `e ↦ Ŕ_e` of `sec:compiler`. That compiler is
assembled, from the branch lemmas of the `higman-compiler`/`hnn-permanence`/
`rope-groups` lanes, into the single hypothesis `Recognition.RecognitionFamily`
(`RecognitionMainTheorem.lean`): a computable `code : Code → PresentationCode`
(`lem:finite-rope`) together with `negative` (`lem:negative-branch`) and
`positive` (`lem:positive-branch`). Every printed clause of `thm:recognition`
is then closed, unconditionally in `R`, by `Recognition.manuscriptRecognition`;
this sentence is its `Π⁰₂`-completeness clause. -/
def PrintedRecognitionPi02Complete : Prop :=
  Pi02Complete (fun c : PresentationCode ↦ IsOperatorMF (Carrier c))

theorem manuscriptRecognitionPi02Complete
    (R : Recognition.RecognitionFamily) : PrintedRecognitionPi02Complete :=
  Recognition.mfPresentations_pi02Complete R

/-- Sentence `c54ed6a64a49`, decidability half: "So it is impossible to
construct an algorithm that decides from a finite presentation whether the
group it defines is MF, ... ". Exactly `no_mf_decider`. -/
theorem manuscriptNoDecider :
    ¬ ∃ f : PresentationCode → Bool,
        Computable f ∧ ∀ c, f c = true ↔ IsOperatorMF (Carrier c) :=
  MFRecognitionImpossible.no_mf_decider

/-- Sentence `c54ed6a64a49`, non-MF enumeration half: "... and impossible
even to enumerate the presentations of MF groups, or those of non-MF
groups." The non-MF-presentations half is exactly `nonMF_presentations_not_re`
(`NONMF ∉ RE`, unconditional). -/
theorem manuscriptNonMFPresentationsNotRE :
    ¬ REPred fun c : PresentationCode => ¬ IsOperatorMF (Carrier c) :=
  MFRecognitionImpossible.nonMF_presentations_not_re

/-- Sentence `c54ed6a64a49`, MF-presentations half of the same clause: the
MF presentations are also not recursively enumerable. Closed by
`Recognition.mfPresentations_not_re`, from the same `RecognitionFamily`
hypothesis `R`: a `Π⁰₂`-complete set is not `Σ⁰₂`, hence not `Σ⁰₁`, made
effective there by reducing `NonhaltsZero` to `MF_fp`. -/
def PrintedMFPresentationsNotRE : Prop :=
  ¬ REPred fun c : PresentationCode => IsOperatorMF (Carrier c)

theorem manuscriptMFPresentationsNotRE
    (R : Recognition.RecognitionFamily) : PrintedMFPresentationsNotRE :=
  Recognition.mfPresentations_not_re R

/-- Sentence `4ee80496e936`: a presentation defines an MF group exactly when
every finite word challenge has either a word-problem witness or a coded
rational unitary microstate with decidable norm certificates.  The `∀∃`
checker normal form is exactly `isOperatorMF_iff_forall_exists_MFChecker`, and
the complete Boolean checker is primitive recursive (`primrec_MFChecker`). -/
theorem manuscriptCheckerCharacterization (c : PresentationCode) :
    IsOperatorMF (Carrier c) ↔
      ∀ n, ∃ cert : ℕ, MFRecognitionPi02.MFChecker c n cert = true :=
  MFRecognitionPi02.isOperatorMF_iff_forall_exists_MFChecker c

/-- Sentence `675d05a8d993`: "We also construct, computably from any
program, a finite presentation that defines an MF group if and only if the
program halts on infinitely many inputs." This is the `e ↦ R̂_e` compiler of
`sec:compiler`, assembled from the seed group `H`, the switch construction,
the three-generator bridge, and the central-rope HNN extensions. -/
def PrintedComputableCompilerConstruction : Prop :=
  ∃ Rhat : Nat.Partrec.Code → PresentationCode, Computable Rhat ∧
    ∀ e : Nat.Partrec.Code,
      IsOperatorMF (Carrier (Rhat e)) ↔ SecondLevelIndexSets.InfiniteDomain e

theorem manuscriptComputableCompilerConstruction
    (R : Recognition.RecognitionFamily) :
    PrintedComputableCompilerConstruction :=
  Recognition.exists_computable_mf_family R

/-- Sentence `31e75269416c`: "If the program halts on only finitely many
inputs, the presented group contains the non-MF group of `[NonMF]`; if it
halts on infinitely many inputs, the group is MF by a permanence theorem for
HNN extensions whose edge isomorphism is implemented by a unitary of a norm
matrix corona." These are `lem:negative-branch` and `lem:positive-branch`,
which are exactly the `negative`/`positive` fields of the very
`RecognitionFamily` whose `code` gives `PrintedComputableCompilerConstruction`
-- so the two sentences share the one hypothesis `R`. -/
def PrintedCompilerBranches (R : Recognition.RecognitionFamily) : Prop :=
  (∀ e : Nat.Partrec.Code, SecondLevelIndexSets.FiniteDomain e →
      ¬ IsOperatorMF (Carrier (R.code e))) ∧
    (∀ e : Nat.Partrec.Code, SecondLevelIndexSets.InfiniteDomain e →
      IsOperatorMF (Carrier (R.code e)))

theorem manuscriptCompilerBranches (R : Recognition.RecognitionFamily) :
    PrintedCompilerBranches R :=
  ⟨R.negative, R.positive⟩

/-! ## `sec:prelim`, "MF groups" -/

/-- Sentences `a7c657eb85c7` + `6201111b83a0`: "A countable group `G` is MF
if there are positive integers `d_n` and maps `V_n : G → U(d_n)`, with
`V_n(1) = 1`, such that `‖V_n(gh) - V_n(g)V_n(h)‖ → 0` `(g,h ∈ G)`, and
`limsup_n ‖V_n(g) - 1‖ > 0` `(g ∈ G ∖ {1})`."

The display's `limsup_n ‖V_n(g) - 1‖ > 0` is operationalized as "there is a
fixed `δ > 0` attained eventually" for every pair of distinct elements, the
form carried by `WeakMFApproximation` and consumed by the rest of the
development; this is the same operationalization already recorded for the
sister sentence in `OneSidedMFRadical.PrintedMFUnitaryModels`. The printed
normalization `V_n(1) = 1` is not separately required by
`WeakMFApproximation` (no field constrains `map n 1`); it is a normalizing
convention that does not change the property (any model can be renormalized
once `map n 1 → 1`, which is what the construction below already provides),
and is not reproved as a separate lemma here. -/
def PrintedMFGroupDefinition (G : Type) [Group G] : Prop :=
  Nonempty (WeakMFApproximation G)

theorem manuscriptMFGroupDefinition (G : Type) [Group G] [Countable G] :
    IsOperatorMF G ↔ PrintedMFGroupDefinition G :=
  isOperatorMF_iff_nonempty_weakMFApproximation G

/- Sentence `297f1fbfa1f5` ("This is the operator norm notion of MF group
introduced by Carrión--Dadarlat--Eckhardt.") is a literature attribution
with no separate checkable content; not formalized. -/

/- Sentence `d7be1aaf4514` ("Here, MF group always means this operator-norm
local-approximation property.") fixes terminology for the rest of the paper;
no separate checkable content; not formalized. -/

/- Sentence `2a0d28e65002` ("The strong-convergence convention also
requires...") describes an alternative, unused convention; it is a remark,
not a claim proved or used below; not formalized. -/

/-- Sentences `05203f9f8c7f` + `bf4989940236`: "Equivalently, `G` embeds in
the unitary group of the norm matrix corona associated to the sequence
`d = (d_n)`, `Q_d = ∏_n M_{d_n}(ℂ) / ⊕_n M_{d_n}(ℂ)`, where `⊕_n M_{d_n}(ℂ)`
is the `c₀`-direct sum of the sequences with `‖x_n‖ → 0`."

The forward direction is `IsCDEOperatorMF`'s own definition with the
strictly-increasing-dimension clause dropped
(`isCDEOperatorMF_exists_coronaEmbedding`); the converse is
`isCDEOperatorMF_of_coronaEmbedding`. Both are literally
`OneSidedMFRadical.PrintedCoronaImagesAndTargets`'s data, reused here for the
present paper's own corona-formulation sentence. -/
theorem manuscriptCoronaFormulation (G : Type) [Group G] [Countable G] :
    IsCDEOperatorMF G ↔
      ∃ d : ℕ → ℕ, ∃ hd : ∀ n, 0 < d n,
        letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
          fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
        ∃ iota : G →* unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))), Function.Injective iota :=
  ⟨fun h ↦ isCDEOperatorMF_exists_coronaEmbedding G h,
    fun ⟨d, hd, iota, hiota⟩ ↦
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      isCDEOperatorMF_of_coronaEmbedding
        G (fun n ↦ naturalFiniteModel (d n)) (fun n ↦ by simpa using hd n)
        iota hiota⟩

/-- Sentence `089abd2aa0ca`: "A separable `C*`-algebra is called MF if it
embeds as a `C*`-subalgebra of a norm matrix corona."

This is `IsMFAlgebra`'s own definition read through the printed
(unrestricted-dimension) convention; `MFAlgebraDimension.isMFAlgebra_iff`
proves the two conventions agree. -/
theorem manuscriptMFAlgebraDefinition (A : Type) [NonUnitalCStarAlgebra A] :
    IsMFAlgebra A ↔
      TopologicalSpace.SeparableSpace A ∧
        MFAlgebraDimension.HasUnrestrictedMFEmbedding A :=
  MFAlgebraDimension.isMFAlgebra_iff A

/-- Sentence `3a88dbf43438`: "Restricting models to a subgroup shows that
subgroups of MF groups are MF." Exactly `IsOperatorMF.subgroup`. -/
theorem manuscriptSubgroupsOfMFAreMF
    {G : Type} [Group G] (H : Subgroup G) (h : IsOperatorMF G) :
    IsOperatorMF H :=
  h.subgroup H

/-- Sentence `76bc4eff61a4`: "Throughout, the binary Leavitt algebra
`L_{𝔽₂}(1,2)` is the unital `𝔽₂`-algebra generated by `s₀,s₁,t₀,t₁` subject
to `t_is_j = δ_{ij}` and `s₀t₀ + s₁t₁ = 1`, and `H = EL₁₂(L_{𝔽₂}(1,2))` is
the subgroup of `GL₁₂(L_{𝔽₂}(1,2))` generated by the elementary matrices
`e_{ij}(a) = 1 + aE_{ij}`, `i ≠ j`."

`R := UniversalLeavitt.BinaryLeavittAlgebra` and
`H := BinaryLeavittSteinberg.ElementaryBase 12`
(`OneSidedMFRadical.RankTwelveEndpoint.R`/`.H`) are exactly these objects;
the two structural facts recorded here (nontriviality and finite generation
of `H`) are what the next sentence's citation of `H` needs. -/
theorem manuscriptBinaryLeavittGroup :
    Nontrivial RankTwelveEndpoint.H ∧ Group.FG RankTwelveEndpoint.H :=
  ⟨RankTwelveEndpoint.nontrivial, RankTwelveEndpoint.finitelyGenerated⟩

/-- Sentence `24a9424a74f6`: "By [Theorem B]{NonMF}, every homomorphism from
`H` to an MF group is trivial; in particular `H` is not MF."

Both clauses are conjuncts of the closed, hypothesis-free
`manuscriptPrintedHeadline` (`PrintedHeadline`, `#audit_closed_axioms`ed in
`Endpoint/OneSidedTransportAudit.lean`), read through `IsCDEOperatorMF`
(the paper's MF convention on `sec:prelim`, equivalent to `IsOperatorMF` by
`isCDEOperatorMF_iff_isOperatorMF`). -/
theorem manuscriptHTheoremB :
    (∀ (M : Type) [Group M] [Countable M], IsOperatorMF M →
      ∀ (f : RankTwelveEndpoint.H →* M) (x : RankTwelveEndpoint.H), f x = 1) ∧
    ¬ IsOperatorMF RankTwelveEndpoint.H := by
  letI : Countable RankTwelveEndpoint.H := RankTwelveEndpoint.countable
  have hheadline := manuscriptPrintedHeadline
  obtain ⟨_hfg, ⟨_hnt, _hsimple, _hT, _hresidual, htrivial, hnotCDE⟩, _hreduced⟩ :=
    hheadline
  refine ⟨fun M _ _ hM f x ↦ ?_, ?_⟩
  · exact htrivial M ((isCDEOperatorMF_iff_isOperatorMF M).mpr hM) f x
  · exact fun hM ↦ hnotCDE ((isCDEOperatorMF_iff_isOperatorMF _).mpr hM)

/-! ## `sec:hnn`, HNN extensions with a corona conjugator (introduction) -/

/- Sentence `1324ce0327e8` ("In [NonMF] we prove non-approximability using
one-sided conjugation in a norm matrix corona.") is a citation to the
companion paper's proof method; not formalized. -/

/-- Sentence `47604663f047`: "If the edge isomorphism of an HNN extension is
implemented by a unitary of a norm matrix corona, then the HNN extension is
MF." This is `thm:hnn-permanence`'s headline conclusion.

The full hypothesis is "`G` admits a tracial MF realization `(A,ρ,τ)` (this is
sentence `2d35e11ad64d`'s object, `RegularRealizationData`), and for some norm
matrix corona `𝒬` there are an injective `*`-homomorphism `ι : A → 𝒬` and a
unitary `W ∈ 𝒬` with `Wιρ(s)W* = ιρ(θ(s))` for `s ∈ S`"; the conclusion here
is `thm:hnn-permanence`'s second sentence alone ("In particular, `R` is MF").
`thm:hnn-permanence` itself is the `hnn-permanence` lane's own module, not yet
on `main`; the field `TensorSynchronization.HNNPermanenceInputs.hnnPermanence`
already carries exactly this statement as a hypothesis, in the `HullInputs`
idiom (`TensorSynchronization.lean`'s own header explains the arrangement),
so the sentence closes against it without waiting on that lane. -/
def PrintedHNNPermanenceHeadline
    (_hIn : TensorSynchronization.HNNPermanenceInputs)
    {G : Type} [Group G] [Countable G] {S T : Subgroup G} (theta : S ≃* T)
    {A : Type} [CStarAlgebra A]
    (realization : HNNCoronaConjugatorSentenceAudit.RegularRealizationData G A)
    {Q : ℕ → FiniteModel} [∀ n, Nonempty (Q n)]
    (iota : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Q n))
    (_hiota : Function.Injective iota)
    (W : unitary (NormMatrixCStarCorona (fun n ↦ Q n))) : Prop :=
  (∀ s : S,
      (W : NormMatrixCStarCorona (fun n ↦ Q n)) *
            iota ((realization.rho (s : G) : unitary A) : A) *
          star (W : NormMatrixCStarCorona (fun n ↦ Q n)) =
        iota ((realization.rho ((theta s : T) : G) : unitary A) : A)) →
    IsOperatorMF (HNNExtension G S T theta)

theorem manuscriptHNNPermanenceHeadline
    (hIn : TensorSynchronization.HNNPermanenceInputs)
    {G : Type} [Group G] [Countable G] {S T : Subgroup G} (theta : S ≃* T)
    {A : Type} [CStarAlgebra A]
    (realization : HNNCoronaConjugatorSentenceAudit.RegularRealizationData G A)
    {Q : ℕ → FiniteModel} [∀ n, Nonempty (Q n)]
    (iota : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Q n))
    (hiota : Function.Injective iota)
    (W : unitary (NormMatrixCStarCorona (fun n ↦ Q n)))
    (hcount : Countable (HNNExtension G S T theta)) :
    PrintedHNNPermanenceHeadline hIn theta realization iota hiota W := by
  haveI := hcount
  exact fun hW ↦
    HNNCoronaConjugatorSentenceAudit.isOperatorMF_of_isRegularlyRealized
      (hIn.hnnPermanence theta realization iota hiota W hW)

/- Sentence `8fcb4c37d063` ("For θ = id this is close to Shulman's theorem
on central HNN extensions; the version below assumes...") is a comparison to
the literature, not a separate checkable claim; not formalized. -/

/- Sentence `a45ab71d52c5` ("The corona unitary implements the edge
isomorphism, while the trace and the left regular representation prove that
the group embeds in the resulting algebra.") is a proof-strategy remark for
`thm:hnn-permanence`; its content is discharged by that theorem
(`hnn-permanence` lane) rather than separately here; not formalized. -/

/-- Sentence `2d35e11ad64d`: "A countable group `G` admits a tracial MF
realization `(A,ρ,τ)` if `A` is a separable unital MF `C*`-algebra,
`ρ : G → U(A)` is a homomorphism, and `τ` is a tracial state on `A` with
`τ(ρ(g)) = 0` for every `g ≠ 1`."

This is exactly `HNNCoronaConjugatorSentenceAudit.RegularRealizationData`
(a bundled witness) together with `IsRegularlyRealized` (its existential
closure), reused verbatim under the printed name. -/
abbrev AdmitsTracialMFRealization (G : Type) [Group G] : Prop :=
  HNNCoronaConjugatorSentenceAudit.IsRegularlyRealized G

theorem admitsTracialMFRealization_iff_isRegularlyRealized
    (G : Type) [Group G] :
    AdmitsTracialMFRealization G ↔
      HNNCoronaConjugatorSentenceAudit.IsRegularlyRealized G :=
  Iff.rfl

/-- Sentence `b89e22ba5034`: "Since `τ(1) = 1`, such a group embeds in
`U(A)`, so it is MF." Exactly the existential form
`isOperatorMF_of_isRegularlyRealized`. -/
theorem manuscriptTracialRealizationImpliesMF
    {G : Type} [Group G] [Countable G]
    (hG : AdmitsTracialMFRealization G) : IsOperatorMF G :=
  HNNCoronaConjugatorSentenceAudit.isOperatorMF_of_isRegularlyRealized hG

/-- Sentence `96784974461f`: "Only the vanishing of `τ` off the identity is
used below; traciality is what the constructions below provide."

Made precise: injectivity of `ρ`, and hence operator-MF-ness of `G`, for a
regular realization need only a **unital linear functional** `τ` vanishing
off the identity on `ρ(G)` -- not the tracial identity `τ(xy) = τ(yx)` or
positivity `τ(x^*x) ≥ 0` carried by `TracialState`. This literally restates
`RegularRealizationData.rho_injective`/`.isOperatorMF`'s proofs with `τ`
weakened to `A →ₗ[ℂ] ℂ` plus `τ(1) = 1`, showing the extra `TracialState`
fields are never invoked. -/
theorem rho_injective_of_unital_vanishing
    {G : Type} [Group G] {A : Type} [CStarAlgebra A]
    (rho : G →* unitary A) (tau : A →ₗ[ℂ] ℂ) (htau1 : tau 1 = 1)
    (hvanish : ∀ g : G, g ≠ 1 → tau (rho g : A) = 0) :
    Function.Injective rho := by
  intro g h hgh
  have hmap : rho (g * h⁻¹) = 1 := by
    rw [map_mul, map_inv, hgh, mul_inv_cancel]
  by_contra hne
  have hprod : g * h⁻¹ ≠ 1 := fun hprod ↦ hne (mul_inv_eq_one.mp hprod)
  have hzero := hvanish (g * h⁻¹) hprod
  have hcoe : ((rho (g * h⁻¹) : unitary A) : A) = 1 := congrArg Subtype.val hmap
  rw [hcoe, htau1] at hzero
  exact one_ne_zero hzero

/-- The consequent operator-MF-ness statement, again for the weakened
`τ`: `mf` (separability and a norm-matrix-corona embedding of `A`) plus
injectivity of `ρ` is all `IsMFAlgebra.isOperatorMF` needs. -/
theorem isOperatorMF_of_unital_vanishing
    {G : Type} [Group G] [Countable G] {A : Type} [CStarAlgebra A]
    (mf : IsMFAlgebra A) (rho : G →* unitary A) (tau : A →ₗ[ℂ] ℂ)
    (htau1 : tau 1 = 1) (hvanish : ∀ g : G, g ≠ 1 → tau (rho g : A) = 0) :
    IsOperatorMF G :=
  mf.2.isOperatorMF rho (rho_injective_of_unital_vanishing rho tau htau1 hvanish)

end Preliminaries
end MFRecognition
end Manuscript
end GroupApproximation
