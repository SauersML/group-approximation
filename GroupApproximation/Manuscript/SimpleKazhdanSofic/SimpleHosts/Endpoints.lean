import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleHosts.NeumannNeumann
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleHosts.Host
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FinitelyPresentedGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Simple hosts without LEF: the endpoints of tex l.477–481

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.477–481 (census row `fc84c012b409`):

> Without LEF, every countable group embeds in a finitely generated simple group~\cite{Gorjuskin,Schupp},
> and even in a simple quotient of a torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio},
> so one simple Kazhdan group contains Higman's universal finitely presented group~\cite{Higman}.

## Formalization

* `manuscriptSentence_countableGroupEmbedsInFGSimpleGroup`: every countable group embeds in a
  finitely generated simple group. The host is in fact infinite and has property (T).
  `NeumannNeumann.exists_twoGenerated_commutator_embedding` puts `Γ` inside `[Δ, Δ]` for an
  infinite `2`-generated `Δ`. `exists_simpleKazhdan_commutator_embedding` then embeds `[Δ, Δ]`
  in the lamplighter host `G_Δ = EL_3(R_Δ)`, which is simple, Kazhdan, infinite and finitely
  generated with no LEF hypothesis.
* `manuscriptSentence_simpleKazhdanGroupContainsEveryFPGroup`: one infinite, finitely
  generated, simple group with property (T) contains every finitely presented group. In
  particular it contains Higman's universal finitely presented group, which is finitely
  presented. The countable group `FPUniversal`, the free product of all `⟨Fin n | t⟩` with
  `t` finite, contains every finitely presented group, and the first endpoint embeds it.

The middle clause is not formalized here: the corpus has no infinite torsion-free hyperbolic
group with property (T) (`Hyperbolic.SharpExistence` is unproved), and a simple quotient must be
nontrivial.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SimpleHosts

/-- **(a) Every countable group embeds in a finitely generated simple group**, which can moreover
be taken infinite with property (T). -/
theorem manuscriptSentence_countableGroupEmbedsInFGSimpleGroup (Γ : Type) [Group Γ]
    [Countable Γ] :
    ∃ (G : Type) (_ : Group G), Group.FG G ∧ IsSimpleGroup G ∧ HasKazhdanPropertyT.{0, 0} G ∧
      Infinite G ∧ ∃ f : Γ →* G, Function.Injective f := by
  obtain ⟨Δ, _, hinf, hfg, f, hf, hcomm⟩ :=
    NeumannNeumann.exists_twoGenerated_commutator_embedding Γ
  haveI : Infinite Δ := hinf
  obtain ⟨G, _, hGinf, hGfg, hGs, hGT, e, he⟩ := exists_simpleKazhdan_commutator_embedding Δ hfg
  refine ⟨G, inferInstance, hGfg, hGs, hGT, hGinf,
    e.comp (f.codRestrict (commutator Δ) hcomm), ?_⟩
  intro x y hxy
  have h1 : e (f.codRestrict (commutator Δ) hcomm x) = e (f.codRestrict (commutator Δ) hcomm y) :=
    hxy
  exact hf (congrArg Subtype.val (he h1))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimpleHosts.manuscriptSentence_countableGroupEmbedsInFGSimpleGroup

/-! ## A countable group containing every finitely presented group -/

/-- Finite presentations `⟨Fin n | t⟩`. -/
abbrev FPIndex : Type := Σ n : ℕ, Finset (FreeGroup (Fin n))

/-- The group `⟨Fin n | t⟩` presented by `i = ⟨n, t⟩`. -/
abbrev FPFactor (i : FPIndex) : Type := PresentedGroup (↑i.2 : Set (FreeGroup (Fin i.1)))

/-- The free product of all finitely presented groups `⟨Fin n | t⟩`. -/
abbrev FPUniversal : Type := Monoid.CoprodI FPFactor

instance fpFactorCountable (i : FPIndex) : Countable (FPFactor i) :=
  (PresentedGroup.mk_surjective _).countable

instance fpUniversalCountable : Countable FPUniversal :=
  Con.mk'_surjective.countable

/-- Every finitely presented group embeds in `FPUniversal`. -/
theorem exists_embedding_fpUniversal (H : Type) [Group H] [Group.IsFinitelyPresented H] :
    ∃ f : H →* FPUniversal, Function.Injective f := by
  obtain ⟨n, s, hs, ⟨e⟩⟩ := Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup (G := H)
  obtain ⟨t, rfl⟩ := hs.exists_finset_coe
  exact ⟨(Monoid.CoprodI.of (M := FPFactor) (i := (⟨n, t⟩ : FPIndex))).comp e.toMonoidHom,
    (Monoid.CoprodI.of_injective (M := FPFactor) (⟨n, t⟩ : FPIndex)).comp e.injective⟩

/-- **(c) One simple Kazhdan group contains every finitely presented group**, in particular
Higman's universal finitely presented group. The group is moreover infinite and finitely
generated. -/
theorem manuscriptSentence_simpleKazhdanGroupContainsEveryFPGroup :
    ∃ (G : Type) (_ : Group G), Infinite G ∧ Group.FG G ∧ IsSimpleGroup G ∧
      HasKazhdanPropertyT.{0, 0} G ∧
      ∀ (H : Type) [Group H] [Group.IsFinitelyPresented H], ∃ f : H →* G, Function.Injective f := by
  obtain ⟨G, _, hfg, hsimple, hT, hinf, f, hf⟩ :=
    manuscriptSentence_countableGroupEmbedsInFGSimpleGroup FPUniversal
  refine ⟨G, inferInstance, hinf, hfg, hsimple, hT, ?_⟩
  intro H _ _
  obtain ⟨g, hg⟩ := exists_embedding_fpUniversal H
  exact ⟨f.comp g, hf.comp hg⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimpleHosts.manuscriptSentence_simpleKazhdanGroupContainsEveryFPGroup

end SimpleHosts
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimpleHosts.exists_embedding_fpUniversal
