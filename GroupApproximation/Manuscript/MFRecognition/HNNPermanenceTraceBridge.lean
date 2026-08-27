import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceCitations
import GroupApproximation.Manuscript.MFRecognition.HNNTraceBaseTrace
import GroupApproximation.Manuscript.MFRecognition.HNNTraceCovariantBase

/-!
# `thm:hnn-permanence`, Step 3: the tracial state

This module assembles the printed Step 3 of `thm:hnn-permanence`:

> *Step 3: the tracial state.*  The functional `T = τ ∘ ι⁻¹` is a tracial state
> on `ι(A) ⊇ D` with `T(ιρ(g)) = 0` for `g ≠ 1`. ... Thus there is a
> `*`-homomorphism `π : D → C*_r(G)` with `π(ιρ(g)) = λ_G(g)`. ... the
> assignment `λ_G(g) ↦ λ_R(g)` extends to a `*`-homomorphism
> `C*_r(G) → C*_r(R)`.  Composing, we obtain `σ₀ : D → C*_r(R)` with
> `σ₀(ιρ(g)) = λ_R(g)`.  The pair `(σ₀, λ_R(t))` satisfies the covariance
> relation `λ_R(t)σ₀(b)λ_R(t)* = σ₀(Θ(b))` for `b ∈ B₀` ... The universal
> property of `U` gives `σ : U → C*_r(R)` ... Define `j : R → 𝒰(U)` ... and
> `σ ∘ j = λ_R` is injective, so `j` is injective.  Let `A' = C*(j(R)) ⊆ U` ...
> and let `τ' = τ_R ∘ σ|_{A'}` ... So `(A', j, τ')` is a tracial MF
> realization of `R`.

It is deliberately thin, and it consumes only *landed* modules.  Most of the
paragraph is now proved elsewhere on main and simply reused here:

* `T = τ ∘ ι⁻¹` and its regularity are `HNNTraceBaseTrace.baseTrace` and
  `baseTrace_regular`, resting on `HNNTraceBaseTransport.HNNTraceBaseRecovery`,
  the inverse of `ι` on `D`;
* `π : D → C*_r(G)` is `HNNTraceReducedFactorization.reducedFactorisation`;
* the coset decomposition giving `C*_r(G) → C*_r(R)` is
  `HNNTraceReducedSubgroup.reducedSubgroupHom`, whose module also proves
  `hnnExtension_countable`;
* `σ₀` and `λ_R(t)` are `HNNTraceCovariantBase.sigmaZero` and `stableUnitary`.

What remains here is the assembly: the covariance relation, the lift `σ`, the
group representation `j`, its faithfulness, the trace `τ'`, and the realization
`(A', j, τ')`.  Exactly one printed sentence of the paragraph is still assumed
rather than proved — *"two `*`-homomorphisms that agree on generators agree on
`B₀`"*, the field `HNNInputs.edgeDensity`, used once, in
`sigmaZero_covariance`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open ReducedGroupCStarTrace

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-! ## The covariance relation -/

/-- The printed identity *"on the generators `ιρ(s)` both sides equal
`λ_R(θ(s))`, because `tst⁻¹ = θ(s)` in `R`"*. -/
theorem sigmaZero_covariance_generator
    (data : CoronaConjugator G S T phi A X) (s : S) :
    (stableUnitary G S T phi :
            ReducedGroupCStar (HNNExtension G S T phi)) *
          sigmaZero data
            (((baseUnitaryHom data (s : G) : unitary (baseAlgebra data)) :
              baseAlgebra data)) *
        star (stableUnitary G S T phi :
          ReducedGroupCStar (HNNExtension G S T phi)) =
      sigmaZero data
        (((baseUnitaryHom data (edgeHom phi s) :
          unitary (baseAlgebra data)) : baseAlgebra data)) := by
  have hgroup : (HNNExtension.t : HNNExtension G S T phi) *
      HNNExtension.of (s : G) * (HNNExtension.t : HNNExtension G S T phi)⁻¹ =
      HNNExtension.of ((phi s : T) : G) := by
    rw [HNNExtension.t_mul_of, mul_assoc, mul_inv_cancel, mul_one]
  rw [sigmaZero_apply, sigmaZero_apply, edgeHom_apply]
  show reducedLeftRegular (HNNExtension G S T phi) HNNExtension.t *
        reducedLeftRegular (HNNExtension G S T phi)
          (HNNExtension.of (s : G)) *
      star (reducedLeftRegular (HNNExtension G S T phi) HNNExtension.t) =
    reducedLeftRegular (HNNExtension G S T phi)
      (HNNExtension.of ((phi s : T) : G))
  rw [star_reducedLeftRegular, ← reducedLeftRegular_mul,
    ← reducedLeftRegular_mul, hgroup]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Printed: *"The pair `(σ₀, λ_R(t))` satisfies the covariance relation
`λ_R(t)σ₀(b)λ_R(t)* = σ₀(Θ(b))` for `b ∈ B₀`."* -/
theorem sigmaZero_covariance (hIn : HNNInputs)
    (data : CoronaConjugator G S T phi A X)
    (b : sourceEdgeAlgebra data) :
    (stableUnitary G S T phi :
          ReducedGroupCStar (HNNExtension G S T phi)) *
        sigmaZero data ((b : baseAlgebra data)) =
      sigmaZero data
          (((edgeIsomorphism data b : targetEdgeAlgebra data) :
            baseAlgebra data)) *
        (stableUnitary G S T phi :
          ReducedGroupCStar (HNNExtension G S T phi)) := by
  have hfg :
      (Unitary.conjStarAlgAut ℂ (ReducedGroupCStar (HNNExtension G S T phi))
              (stableUnitary G S T phi)).toStarAlgHom.comp
          ((sigmaZero data).comp (sourceEdgeAlgebra data).subtype) =
        (sigmaZero data).comp
          ((targetEdgeAlgebra data).subtype.comp
            (edgeIsomorphism data).toStarAlgHom) := by
    refine hIn.edgeDensity data _ _ ?_
    intro s
    show (stableUnitary G S T phi :
              ReducedGroupCStar (HNNExtension G S T phi)) *
            sigmaZero data
              ((((sourceGenerator data s :
                unitary (sourceEdgeAlgebra data)) : sourceEdgeAlgebra data) :
                baseAlgebra data)) *
          star (stableUnitary G S T phi :
            ReducedGroupCStar (HNNExtension G S T phi)) =
      sigmaZero data
        (((edgeIsomorphism data
            (((sourceGenerator data s : unitary (sourceEdgeAlgebra data)) :
              sourceEdgeAlgebra data)) : targetEdgeAlgebra data) :
          baseAlgebra data))
    rw [edgeIsomorphism_generator, coe_sourceGenerator, coe_targetGenerator]
    exact sigmaZero_covariance_generator data s
  have hb := congrArg
    (fun F : sourceEdgeAlgebra data →⋆ₐ[ℂ]
        ReducedGroupCStar (HNNExtension G S T phi) ↦ F b) hfg
  have hstar : star (stableUnitary G S T phi :
        ReducedGroupCStar (HNNExtension G S T phi)) *
      (stableUnitary G S T phi :
        ReducedGroupCStar (HNNExtension G S T phi)) = 1 :=
    (stableUnitary G S T phi).property.1
  have h : (stableUnitary G S T phi :
            ReducedGroupCStar (HNNExtension G S T phi)) *
          sigmaZero data ((b : baseAlgebra data)) *
        star (stableUnitary G S T phi :
          ReducedGroupCStar (HNNExtension G S T phi)) =
      sigmaZero data
        (((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data)) := hb
  rw [← h, mul_assoc, hstar, mul_one]

/-- The printed covariant pair `(σ₀, λ_R(t))`. -/
def reducedCovariantRepresentation (hIn : HNNInputs)
    (data : CoronaConjugator G S T phi A X) :
    CStarHNNRepresentation (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
      (edgeIsomorphism data) :=
  CStarHNNRepresentation.ofCovariantPair (sourceEdgeAlgebra data)
    (targetEdgeAlgebra data) (edgeIsomorphism data)
    (sigmaZero data) (stableUnitary G S T phi)
    (sigmaZero_covariance hIn data)

/-- Printed: *"The universal property of `U` gives `σ : U → C*_r(R)` with
`σ(ιρ(g)) = λ_R(g)` and `σ(u) = λ_R(t)`."* -/
def sigma (hIn : HNNInputs) (data : CoronaConjugator G S T phi A X) :
    universalHNN data →⋆ₐ[ℂ] ReducedGroupCStar (HNNExtension G S T phi) :=
  universalCStarHNNEval (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
    (edgeIsomorphism data) (reducedCovariantRepresentation hIn data)

@[simp] theorem sigma_base (hIn : HNNInputs)
    (data : CoronaConjugator G S T phi A X) (d : baseAlgebra data) :
    sigma hIn data (universalBase data d) = sigmaZero data d :=
  rfl

@[simp] theorem sigma_stable (hIn : HNNInputs)
    (data : CoronaConjugator G S T phi A X) :
    sigma hIn data
        ((universalStable data : unitary (universalHNN data)) :
          universalHNN data) =
      (stableUnitary G S T phi :
        ReducedGroupCStar (HNNExtension G S T phi)) :=
  rfl

/-! ## `j : R → 𝒰(U)` -/

/-- The base-group representation `g ↦ ιρ(g)` inside `U`. -/
def universalBaseUnitary (data : CoronaConjugator G S T phi A X) :
    G →* unitary (universalHNN data) :=
  (unitaryMapOfStarAlgHom (universalBase data)).comp (baseUnitaryHom data)

/-- Printed: *"The defining relations of `eq:hnn` hold in `U`, since
`u ιρ(s) u* = Θ(ιρ(s)) = ιρ(θ(s))`."* -/
theorem universalBaseUnitary_covariance
    (data : CoronaConjugator G S T phi A X) (s : S) :
    universalStable data * universalBaseUnitary data (s : G) =
      universalBaseUnitary data ((phi s : T) : G) * universalStable data := by
  apply Subtype.ext
  have h := universalCStarHNN_covariance (sourceEdgeAlgebra data)
    (targetEdgeAlgebra data) (edgeIsomorphism data)
    ((sourceGenerator data s : unitary (sourceEdgeAlgebra data)) :
      sourceEdgeAlgebra data)
  have hgen := congrArg
    (fun z : targetEdgeAlgebra data ↦
      universalBase data ((z : baseAlgebra data)) *
        ((universalStable data : unitary (universalHNN data)) :
          universalHNN data))
    (edgeIsomorphism_generator data s)
  exact h.trans hgen

/-- Printed: *"Define `j : R → 𝒰(U)` by `j(g) = ιρ(g)` for `g ∈ G` and
`j(t) = u`"*. -/
def groupLift (data : CoronaConjugator G S T phi A X) :
    HNNExtension G S T phi →* unitary (universalHNN data) :=
  universalCStarHNNGroupLift (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
    (edgeIsomorphism data) phi (universalBaseUnitary data)
    (universalBaseUnitary_covariance data)

@[simp] theorem groupLift_of (data : CoronaConjugator G S T phi A X) (g : G) :
    groupLift data (HNNExtension.of g) = universalBaseUnitary data g :=
  universalCStarHNNGroupLift_of _ _ _ _ _ _ g

@[simp] theorem groupLift_t (data : CoronaConjugator G S T phi A X) :
    groupLift data HNNExtension.t = universalStable data :=
  universalCStarHNNGroupLift_t _ _ _ _ _ _

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Printed: *"`σ ∘ j = λ_R`"*. -/
theorem groupLiftEval_eq_regular (hIn : HNNInputs)
    (data : CoronaConjugator G S T phi A X) :
    universalCStarHNNGroupLiftEval (sourceEdgeAlgebra data)
        (targetEdgeAlgebra data) (edgeIsomorphism data) phi
        (reducedCovariantRepresentation hIn data)
        (universalBaseUnitary data)
        (universalBaseUnitary_covariance data) =
      reducedLeftRegularUnitaryHom (HNNExtension G S T phi) := by
  refine HNNExtension.hom_ext ?_ ?_
  · refine MonoidHom.ext fun g ↦ ?_
    apply Subtype.ext
    show sigma hIn data
        ((groupLift data (HNNExtension.of g) : unitary (universalHNN data)) :
          universalHNN data) =
      reducedLeftRegular (HNNExtension G S T phi) (HNNExtension.of g)
    rw [groupLift_of]
    exact sigmaZero_apply data g
  · apply Subtype.ext
    show sigma hIn data
        ((groupLift data HNNExtension.t : unitary (universalHNN data)) :
          universalHNN data) =
      reducedLeftRegular (HNNExtension G S T phi) HNNExtension.t
    exact congrArg
      (fun u : unitary (universalHNN data) ↦
        sigma hIn data (u : universalHNN data))
      (groupLift_t data)

/-- Printed: *"`σ ∘ j = λ_R` is injective, so `j` is injective."* -/
theorem groupLift_injective (hIn : HNNInputs)
    (data : CoronaConjugator G S T phi A X) :
    Function.Injective (groupLift data) := by
  apply universalCStarHNN_groupLift_injective (sourceEdgeAlgebra data)
    (targetEdgeAlgebra data) (edgeIsomorphism data) phi
    (reducedCovariantRepresentation hIn data) (universalBaseUnitary data)
    (universalBaseUnitary_covariance data)
  rw [groupLiftEval_eq_regular]
  exact reducedLeftRegularUnitaryHom_injective (HNNExtension G S T phi)

/-! ## The trace `τ' = τ_R ∘ σ` -/

/-- The pullback of the canonical trace `τ_R` of `C*_r(R)` along `σ`. -/
def universalTrace (hIn : HNNInputs)
    (data : CoronaConjugator G S T phi A X) :
    TracialState (universalHNN data) :=
  ((canonicalFaithfulTracialState
    (HNNExtension G S T phi)).toTracialState).compStarAlgHom
      (sigma hIn data)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Printed: *"`τ'(j(r)) = τ_R(λ_R(r)) = 0` for `r ≠ 1`."* -/
theorem universalTrace_regular (hIn : HNNInputs)
    (data : CoronaConjugator G S T phi A X)
    (r : HNNExtension G S T phi) (hr : r ≠ 1) :
    universalTrace hIn data
        (((groupLift data r : unitary (universalHNN data)) :
          universalHNN data)) = 0 := by
  have hlambda : sigma hIn data
      (((groupLift data r : unitary (universalHNN data)) :
        universalHNN data)) =
      reducedLeftRegular (HNNExtension G S T phi) r := by
    have h := congrArg (fun f : HNNExtension G S T phi →*
        unitary (ReducedGroupCStar (HNNExtension G S T phi)) ↦ f r)
      (groupLiftEval_eq_regular hIn data)
    exact congrArg Subtype.val h
  show ((canonicalFaithfulTracialState
      (HNNExtension G S T phi)).toTracialState)
      (sigma hIn data
        (((groupLift data r : unitary (universalHNN data)) :
          universalHNN data))) = 0
  rw [hlambda]
  exact canonicalCoefficientAtOne_reducedLeftRegular_of_ne_one
    (HNNExtension G S T phi) hr

/-! ## `(A', j, τ')` -/

/-- Printed: *"So `(A', j, τ')` is a tracial MF realization of `R`."*  The MF
property of the ambient `U` is the conclusion of Steps 1 and 2, entering as
`HNNInputs.universalHNNIsMF`; `HNNPermanenceShulman` discharges that
proposition from Ueda's corner model and Shulman's criterion, so the printed
proof route is the route taken. -/
def hnnRegularRealization (hIn : HNNInputs) [Countable G]
    (data : CoronaConjugator G S T phi A X) :
    RegularRealizationData (HNNExtension G S T phi)
      (groupGeneratedCStar (groupLift data)) := by
  letI : Countable (HNNExtension G S T phi) :=
    hnnExtension_countable G S T phi
  exact generatedRegularRealization
    (hIn.universalHNNIsMF data).2
    (groupLift data) (universalTrace hIn data)
    (fun r hr ↦ universalTrace_regular hIn data r hr)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
