import GroupApproximation.BooneHigman.Products.Assembly

/-!
# Hosts for the product step

The host lanes produce faithful self-similar actions of finitely presented groups, as
representations `ρ : Γ →* Aut(T_X)` with `Trees.IsSelfSimilarRep ρ`.  This module turns such a
representation into membership in `EmbedsInFPSelfSimilarGroup`, and records the linear endpoint T3
in terms of Zaremsky's envelope theorem and a linear host statement.

* `embedsInFPSelfSimilarGroup_of_rep`: a finitely presented group with a faithful self-similar
  action embeds in a finitely presented self-similar group.
* `LinearHostStatement`: every finitely generated subgroup of `GL_n(K)` embeds in a finitely
  presented self-similar group.
* `finitelyGeneratedLinearStatement_of_hosts`: T3 from the linear host statement and the envelope
  theorem.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Products

open Trees

/-- A finitely presented group with a faithful self-similar action on a finite alphabet with at least
two letters embeds in a finitely presented self-similar group: its image. -/
theorem embedsInFPSelfSimilarGroup_of_rep {Γ : Type*} [Group Γ] [Group.IsFinitelyPresented Γ]
    {X : Type} [Finite X] [Nontrivial X] (ρ : Γ →* TreeAut X) (hρ : IsSelfSimilarRep ρ) :
    EmbedsInFPSelfSimilarGroup Γ := by
  haveI : Group.IsFinitelyPresented ρ.range :=
    Group.IsFinitelyPresented.equiv (MonoidHom.ofInjective hρ.1)
  exact ⟨X, inferInstance, inferInstance, ρ.range, hρ.2, inferInstance,
    (MonoidHom.ofInjective hρ.1).toMonoidHom, (MonoidHom.ofInjective hρ.1).injective⟩

/-- **The linear host statement**: every finitely generated subgroup of `GL_n(K)`, for any field
`K`, embeds in a finitely presented self-similar group. -/
def LinearHostStatement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)),
    H.FG → EmbedsInFPSelfSimilarGroup H

/-- **T3 from the linear host statement and the envelope theorem.** -/
theorem finitelyGeneratedLinearStatement_of_hosts (hlin : LinearHostStatement)
    (henv : FPSelfSimilarEnvelopeStatement) : FinitelyGeneratedLinearStatement :=
  fun K _ n H hH => (hlin K n H hH).embedsInFinitelyPresentedSimpleGroup henv

end Products
end BooneHigman
end GroupApproximation
