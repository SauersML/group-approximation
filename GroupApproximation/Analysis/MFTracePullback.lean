import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Analysis.ShulmanTraceClasses

/-!
# MF traces pull back along `⋆`-homomorphisms

Shulman's MF-trace condition is a statement about *matrix models*, and matrix
models compose with maps into the algebra they model.  This file proves the
two structural facts that follow, and the one instance of them that the
`INT.11` route needs.

## The two facts

* `ShulmanTrace.MFTraceModel.congr` --- the condition depends on the trace
  only through its values, so a pointwise equality of traces transports a
  model.  Needed because the same functional reaches the two sides of the
  route under two different names.
* `ShulmanTrace.MFTraceModel.comp` --- if `τ` is an MF trace on `B` and
  `π : A →⋆ₐ[ℂ] B` is any `⋆`-homomorphism, then `τ ∘ π` is an MF trace on
  `A`, witnessed by `φₙ ∘ π`.  Each of the five clauses transports for the
  same reason: `π` is *exactly* multiplicative, linear and `⋆`-preserving,
  so it moves through the asymptotic defects without contributing to them.

Note which way this goes.  The models get *harder* to find as the algebra
grows, so pulling back along `π` --- from the target to the source --- is the
direction that is free.  Nothing here needs `π` surjective, isometric or
injective.

## The instance the route needs

The canonical trace of the maximal group C⋆-algebra is *defined* as the
canonical trace of the reduced algebra pulled back along the canonical map
`q : C⋆(G) → C⋆_r(G)` (`canonicalMaximalTrace`, whose defining equation
`canonicalMaximalTrace_apply` is definitional).  So
`isMFTrace_canonicalMaximal_of_reducedTrace` is exactly `comp` at `π = q`,
and it converts a statement about the *reduced* algebra --- which is where
quasidiagonality theorems live, and where the canonical trace is faithful ---
into a statement about the *maximal* algebra, which is where
`ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal` consumes it.

This is worth isolating because it is the step that would otherwise be
mistaken for an appeal to Hulanicki's theorem.  Identifying `C⋆(G)` with
`C⋆_r(G)` for amenable `G` is a genuine literature input; **it is not used
here and is not needed**.  The pullback runs along the canonical map for every
group, amenable or not, and the amenability enters this development only where
the quasidiagonality input does.
-/

namespace GroupApproximation
namespace ShulmanTrace

open Filter Matrix ReducedGroupCStarTrace
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]
variable {B : Type v} [Ring B] [StarRing B] [Algebra ℂ B]

/-! ## Transport along an equality of traces -/

/-- An MF-trace model for `τ` is one for `σ` whenever the two functionals
agree pointwise.  Only the trace clause mentions the functional at all. -/
def MFTraceModel.congr {τ σ : A → ℂ} (M : MFTraceModel τ)
    (h : ∀ a : A, τ a = σ a) : MFTraceModel σ where
  space := M.space
  map := M.map
  tendsto_mul := M.tendsto_mul
  tendsto_linear := M.tendsto_linear
  tendsto_star := M.tendsto_star
  bounded := M.bounded
  tendsto_trace a := by simpa only [h] using M.tendsto_trace a

theorem IsMFTrace.congr {τ σ : A → ℂ} (h : IsMFTrace τ)
    (hσ : ∀ a : A, τ a = σ a) : IsMFTrace σ := by
  obtain ⟨M⟩ := h
  exact ⟨M.congr hσ⟩

/-! ## Pullback along a `⋆`-homomorphism -/

/-- **MF traces pull back.**  Composing the matrix models of `τ` with a
`⋆`-homomorphism `π : A →⋆ₐ[ℂ] B` gives matrix models for `τ ∘ π`.

Each clause is the corresponding clause of `M` read at `π a`, `π b`: the
multiplicative defect at `(a, b)` becomes the defect at `(π a, π b)` because
`π (a * b) = π a * π b` *exactly*, and likewise for the linear and adjoint
defects.  The bound and the trace clause are transcribed unchanged. -/
def MFTraceModel.comp {τ : B → ℂ} (M : MFTraceModel τ) (π : A →⋆ₐ[ℂ] B) :
    MFTraceModel (fun a : A ↦ τ (π a)) where
  space := M.space
  map := fun n a ↦ M.map n (π a)
  tendsto_mul a b := by
    simpa only [map_mul] using M.tendsto_mul (π a) (π b)
  tendsto_linear l m a b := by
    simpa only [map_add, map_smul] using M.tendsto_linear l m (π a) (π b)
  tendsto_star a := by
    simpa only [map_star] using M.tendsto_star (π a)
  bounded a := M.bounded (π a)
  tendsto_trace a := M.tendsto_trace (π a)

theorem IsMFTrace.comp {τ : B → ℂ} (h : IsMFTrace τ) (π : A →⋆ₐ[ℂ] B) :
    IsMFTrace (fun a : A ↦ τ (π a)) := by
  obtain ⟨M⟩ := h
  exact ⟨M.comp π⟩

/-! ## The canonical traces of the two group C⋆-algebras -/

variable (G : Type u) [Group G]

/-- The defining factorization of the canonical maximal trace, read through
the faithful tracial state of the reduced algebra.

Both sides unfold to `canonicalCoefficientAtOne G (q a)`: the maximal trace is
defined that way, and `canonicalFaithfulTracialState` is that same functional
with its faithfulness and traciality attached. -/
theorem canonicalFaithfulTracialState_maximalGroupCStarToReduced
    (a : MaximalGroupCStar G) :
    ReducedGroupCStarTrace.canonicalFaithfulTracialState G
        (maximalGroupCStarToReduced G a)
      = canonicalMaximalTrace G a :=
  rfl

/-- **From the reduced algebra to the maximal one.**  If the canonical
faithful trace of `C⋆_r(G)` is an MF trace, so is the canonical trace of
`C⋆(G)`.

This is `MFTraceModel.comp` along the canonical map, and it is the shape
`ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal` consumes.  No
identification of the two algebras is involved, so no amenability and no
Hulanicki input. -/
theorem isMFTrace_canonicalMaximal_of_reducedTrace
    (h : IsMFTrace (fun T : ReducedGroupCStar G ↦
      ReducedGroupCStarTrace.canonicalFaithfulTracialState G T)) :
    IsMFTrace (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) :=
  (h.comp (maximalGroupCStarToReduced G)).congr
    (canonicalFaithfulTracialState_maximalGroupCStarToReduced G)

end

end ShulmanTrace
end GroupApproximation
