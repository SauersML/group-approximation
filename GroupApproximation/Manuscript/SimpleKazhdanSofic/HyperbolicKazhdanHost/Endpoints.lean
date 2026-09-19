import GroupApproximation.Manuscript.SimpleKazhdanSofic.HyperbolicKazhdanHost.Admissible
import GroupApproximation.GGT.HullSCGreendlingerForms
import GroupApproximation.Kazhdan.KotowskiOllivierClosed
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterHost
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleHosts.Endpoints
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Data.Countable.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Simple quotients of a torsion-free hyperbolic Kazhdan group: tex l.477–481

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.477–481 (census row
`fc84c012b409`):

> Without LEF, every countable group embeds in a finitely generated simple group~\cite{Gorjuskin,Schupp},
> and even in a simple quotient of a torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio},
> so one simple Kazhdan group contains Higman's universal finitely presented group~\cite{Higman}.

Clauses (a) and (c) are closed in `SimpleHosts.Endpoints`. This module proves the middle
clause (b) along the Coulon–Fournier-Facio route.

## The proof of (b)

1. **The host.** `Hyperbolic.sharpExistence_closed` (Kotowski–Ollivier, closed in the corpus)
   gives an infinite, finitely presented, torsion-free hyperbolic group `H` with property (T).
   `H` is finitely generated (`KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT`), hence
   countable. One `H` serves every `Γ`.
2. **The ambient group.** Given a countable group `Γ`, set `Γ' = Γ × ℤ`. Then `Γ'` has the
   nontrivial element `γ₀ = (1, 1)`, and `E = H ∗ Γ'` is countable.
3. **The limit.** `limitScheme` makes the admissible kernels of `E` a `LimitScheme`, using
   Hull's Theorem 7.1 and the residual geometry. `LimitScheme.exists_simple_quotient` gives
   `K ◁ E` with:
   - `E ⧸ K` simple;
   - every coset meeting `H`, so `H → E ⧸ K` is onto;
   - every element of `K` killed by an admissible kernel, so `Γ' → E ⧸ K` is injective
     (`injective_mk_inr`).
4. **The embedding.** `Γ → Γ'` is injective.

## Dependencies

* `HullSC.HullOneStepStatementGeneral.{0}` (Hull, Theorem 7.1, every ambient group). The corpus
  proves it from the least-area Greendlinger leaf
  `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}` via
  `HullSC.hullOneStepStatementGeneral_of_greendlinger`. That leaf is in progress, so the
  `_of_greendlinger_of_geometry` endpoint is conditional on it.
* `CoulonFournierFacioGeometryStatement` (module `Admissible`), the one isolated residual:
  - (G1) the start geometry of `H ∗ Γ`;
  - (G2) Osin's Lemma 7.1 in general form together with Hull's finite-normalized-subgroup
    lemma.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace HyperbolicKazhdanHost

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- The limit quotient of `H ∗ Γ`: simple, a quotient of `H`, containing `Γ`. -/
theorem exists_simple_quotient_embedding (hhull : HullSC.HullOneStepStatementGeneral.{0})
    (hgeom : CoulonFournierFacioGeometryStatement) (H Γ : Type) [Group H] [Group Γ]
    [Countable H] [Countable Γ] {γ₀ : Γ} (hγ₀ : γ₀ ≠ 1) (hinf : Infinite H)
    (htf : IsPowerTorsionFree H) (hhyp : Hyperbolic.IsHyperbolicGroup H)
    (hT : HasKazhdanPropertyT.{0, 0} H) :
    ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧ (∃ π : H →* S, Function.Surjective π) ∧
      ∃ f : Γ →* S, Function.Injective f := by
  haveI : Countable (Monoid.Coprod H Γ) :=
    (Monoid.Coprod.mk_surjective (M := H) (N := Γ)).countable
  obtain ⟨K, _, hsimple, hpush, hadm⟩ :=
    (limitScheme hhull hgeom H Γ hγ₀ hinf htf hhyp hT).exists_simple_quotient
  have hadm' : ∀ z ∈ K, ∃ K', IsAdmissible K' ∧ z ∈ K' := hadm
  refine ⟨Monoid.Coprod H Γ ⧸ K, inferInstance, hsimple,
    ⟨(QuotientGroup.mk' K).comp (Monoid.Coprod.inl : H →* Monoid.Coprod H Γ), ?_⟩,
    (QuotientGroup.mk' K).comp (Monoid.Coprod.inr : Γ →* Monoid.Coprod H Γ),
    injective_mk_inr hadm'⟩
  intro w
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨p, hp, hpc⟩ := hpush c
  have hp' : p ∈ (Monoid.Coprod.inl : H →* Monoid.Coprod H Γ).range := hp
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hp'
  exact ⟨h, QuotientGroup.eq.2 hpc⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.exists_simple_quotient_embedding

/-- **(b), from Hull's theorem and the residual geometry.** One infinite, finitely presented,
torsion-free hyperbolic group with property (T) has, for every countable group `Γ`, a simple
quotient containing `Γ`. -/
theorem simpleQuotientOfHyperbolicKazhdan_of_hull_of_geometry
    (hhull : HullSC.HullOneStepStatementGeneral.{0})
    (hgeom : CoulonFournierFacioGeometryStatement) :
    ∃ (H : Type) (_ : Group H), Infinite H ∧ Group.IsFinitelyPresented H ∧
      IsPowerTorsionFree H ∧ Hyperbolic.IsHyperbolicGroup H ∧ HasKazhdanPropertyT.{0, 0} H ∧
      ∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧
        (∃ π : H →* S, Function.Surjective π) ∧ ∃ f : Γ →* S, Function.Injective f := by
  obtain ⟨H, _, hinf, hfp, htf, hhyp, hT⟩ := Hyperbolic.sharpExistence_closed
  refine ⟨H, inferInstance, hinf, hfp, htf, hhyp, hT, ?_⟩
  intro Γ _ _
  haveI : Countable H :=
    Lamplighter.countable_of_fg H (KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT H hT)
  haveI : Countable (Multiplicative ℤ) := inferInstanceAs (Countable ℤ)
  have hγ₀ : (((1 : Γ), Multiplicative.ofAdd (1 : ℤ)) : Γ × Multiplicative ℤ) ≠ 1 := by
    intro h
    have h2 : Multiplicative.ofAdd (1 : ℤ) = 1 := congrArg Prod.snd h
    exact one_ne_zero (ofAdd_eq_one.1 h2)
  obtain ⟨S, _, hsimple, hπ, f, hf⟩ :=
    exists_simple_quotient_embedding hhull hgeom H (Γ × Multiplicative ℤ) hγ₀ hinf htf hhyp hT
  refine ⟨S, inferInstance, hsimple, hπ, f.comp (MonoidHom.inl Γ (Multiplicative ℤ)), ?_⟩
  intro a b hab
  have hab' : f (MonoidHom.inl Γ (Multiplicative ℤ) a) =
      f (MonoidHom.inl Γ (Multiplicative ℤ) b) := hab
  have h2 : a = b := congrArg Prod.fst (hf hab')
  exact h2

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.simpleQuotientOfHyperbolicKazhdan_of_hull_of_geometry

/-- **(b), over the least-area Greendlinger leaf and the residual geometry.** -/
theorem simpleQuotientOfHyperbolicKazhdan_of_greendlinger_of_geometry
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hgeom : CoulonFournierFacioGeometryStatement) :
    ∃ (H : Type) (_ : Group H), Infinite H ∧ Group.IsFinitelyPresented H ∧
      IsPowerTorsionFree H ∧ Hyperbolic.IsHyperbolicGroup H ∧ HasKazhdanPropertyT.{0, 0} H ∧
      ∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧
        (∃ π : H →* S, Function.Surjective π) ∧ ∃ f : Γ →* S, Function.Injective f :=
  simpleQuotientOfHyperbolicKazhdan_of_hull_of_geometry
    (HullSC.hullOneStepStatementGeneral_of_greendlinger hgreendlinger) hgeom

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.simpleQuotientOfHyperbolicKazhdan_of_greendlinger_of_geometry

/-- **The whole sentence of tex l.477–481**:

* (a) every countable group embeds in a finitely generated simple group;
* (b) one torsion-free hyperbolic Kazhdan group has a simple quotient containing any given
  countable group;
* (c) one simple Kazhdan group contains every finitely presented group, Higman's universal
  one included.

(a) and (c) are closed (`SimpleHosts`). (b) rests on the Greendlinger leaf and the residual
geometry. -/
theorem manuscriptSentence_withoutLEFSimpleHosts_of_greendlinger_of_geometry
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hgeom : CoulonFournierFacioGeometryStatement) :
    (∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (G : Type) (_ : Group G), Group.FG G ∧
        IsSimpleGroup G ∧ ∃ f : Γ →* G, Function.Injective f) ∧
      (∃ (H : Type) (_ : Group H), Infinite H ∧ Group.IsFinitelyPresented H ∧
        IsPowerTorsionFree H ∧ Hyperbolic.IsHyperbolicGroup H ∧ HasKazhdanPropertyT.{0, 0} H ∧
        ∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧
          (∃ π : H →* S, Function.Surjective π) ∧ ∃ f : Γ →* S, Function.Injective f) ∧
      ∃ (G : Type) (_ : Group G), IsSimpleGroup G ∧ HasKazhdanPropertyT.{0, 0} G ∧
        ∀ (H : Type) [Group H] [Group.IsFinitelyPresented H],
          ∃ f : H →* G, Function.Injective f := by
  refine ⟨?_, simpleQuotientOfHyperbolicKazhdan_of_greendlinger_of_geometry hgreendlinger hgeom,
    ?_⟩
  · intro Γ _ _
    obtain ⟨G, _, hfg, hs, _, _, f, hf⟩ :=
      SimpleHosts.manuscriptSentence_countableGroupEmbedsInFGSimpleGroup Γ
    exact ⟨G, inferInstance, hfg, hs, f, hf⟩
  · obtain ⟨G, _, _, _, hs, hT, hemb⟩ :=
      SimpleHosts.manuscriptSentence_simpleKazhdanGroupContainsEveryFPGroup
    exact ⟨G, inferInstance, hs, hT, hemb⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.manuscriptSentence_withoutLEFSimpleHosts_of_greendlinger_of_geometry

end HyperbolicKazhdanHost
end SimpleKazhdanSofic
end GroupApproximation
