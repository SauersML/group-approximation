/-!
A Lean 4 skeleton for the final logical chains in the hyperlinear-versus-sofic
problem.  The unresolved analytic and group-theoretic inputs are explicit
hypotheses; no axiom and no `sorry` is introduced here.

Intended toolchain: Lean 4.32.x.
-/

namespace HyperlinearSoficFinalChain

universe u v w z

/-- The universal statement "every hyperlinear object is sofic". -/
def EveryHyperlinearIsSofic
    {GroupLike : Type u}
    (Hyperlinear Sofic : GroupLike -> Prop) : Prop :=
  forall G, Hyperlinear G -> Sofic G

/-- A single hyperlinear nonsofic candidate refutes the universal statement. -/
theorem candidate_hyperlinear_refutes
    {GroupLike : Type u}
    (Hyperlinear Sofic : GroupLike -> Prop)
    {candidate : GroupLike}
    (hHyperlinear : Hyperlinear candidate)
    (hNonsofic : Not (Sofic candidate)) :
    Not (EveryHyperlinearIsSofic Hyperlinear Sofic) := by
  intro hUniversal
  exact hNonsofic (hUniversal candidate hHyperlinear)

/-- Abstract finite-window persistence. -/
def Persists
    {Window : Type v} {Approximation : Type w}
    (Feasible : Window -> Approximation -> Prop) : Prop :=
  forall W, exists A, Feasible W A

/-- Persistence refutes the universal statement once persistence is known to
imply hyperlinearity of a nonsofic candidate. -/
theorem persistence_refutes
    {GroupLike : Type u}
    (Hyperlinear Sofic : GroupLike -> Prop)
    {candidate : GroupLike}
    {Window : Type v} {Approximation : Type w}
    (Feasible : Window -> Approximation -> Prop)
    (persistence_to_hyperlinear :
      Persists Feasible -> Hyperlinear candidate)
    (hPersists : Persists Feasible)
    (hNonsofic : Not (Sofic candidate)) :
    Not (EveryHyperlinearIsSofic Hyperlinear Sofic) := by
  apply candidate_hyperlinear_refutes Hyperlinear Sofic
  · exact persistence_to_hyperlinear hPersists
  · exact hNonsofic

/-- An abstract uniform finite-window gap. -/
def UniformGap
    {Window : Type v} {Approximation : Type w}
    (Feasible : Window -> Approximation -> Prop) : Prop :=
  exists W, forall A, Not (Feasible W A)

/-- A proved implication from a uniform gap to nonhyperlinearity excludes the
candidate.  Notice that this theorem does not assert the universal converse. -/
theorem uniform_gap_excludes_candidate
    {GroupLike : Type u}
    (Hyperlinear : GroupLike -> Prop)
    {candidate : GroupLike}
    {Window : Type v} {Approximation : Type w}
    (Feasible : Window -> Approximation -> Prop)
    (gap_to_nonhyperlinear :
      UniformGap Feasible -> Not (Hyperlinear candidate))
    (hGap : UniformGap Feasible) :
    Not (Hyperlinear candidate) := by
  exact gap_to_nonhyperlinear hGap

/-- The candidate itself satisfies the ordinary classical dichotomy, but the
negative branch only excludes this candidate. -/
theorem candidate_dichotomy
    {GroupLike : Type u}
    (Hyperlinear : GroupLike -> Prop)
    (candidate : GroupLike) :
    Hyperlinear candidate \/ Not (Hyperlinear candidate) := by
  exact Classical.em (Hyperlinear candidate)

/-- Abstract form of the new action-level no-go theorem: if every
"hyperlinear-category sofic action" in a specified class is classically sofic,
then a classically nonsofic action cannot satisfy the stronger hypothesis. -/
theorem action_shortcut_closed
    {Action : Type z}
    (HyperActionSofic ClassicalActionSofic : Action -> Prop)
    {alpha : Action}
    (collapse : forall a, HyperActionSofic a -> ClassicalActionSofic a)
    (hNotClassical : Not (ClassicalActionSofic alpha)) :
    Not (HyperActionSofic alpha) := by
  intro hHyperAction
  exact hNotClassical (collapse alpha hHyperAction)

/-- Even after excluding one candidate, a different hyperlinear nonsofic object
would still refute the universal statement.  This records the logical reason
why candidate nonhyperlinearity is not a proof of the universal implication. -/
theorem different_counterexample_still_refutes
    {GroupLike : Type u}
    (Hyperlinear Sofic : GroupLike -> Prop)
    {candidate other : GroupLike}
    (_candidate_is_nonhyperlinear : Not (Hyperlinear candidate))
    (other_is_hyperlinear : Hyperlinear other)
    (other_is_nonsofic : Not (Sofic other)) :
    Not (EveryHyperlinearIsSofic Hyperlinear Sofic) := by
  exact candidate_hyperlinear_refutes Hyperlinear Sofic
    other_is_hyperlinear other_is_nonsofic

#print axioms candidate_hyperlinear_refutes
#print axioms persistence_refutes
#print axioms uniform_gap_excludes_candidate
#print axioms action_shortcut_closed
#print axioms different_counterexample_still_refutes

end HyperlinearSoficFinalChain
