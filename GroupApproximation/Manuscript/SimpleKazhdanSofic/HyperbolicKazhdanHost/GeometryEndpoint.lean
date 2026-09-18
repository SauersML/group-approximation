import GroupApproximation.Manuscript.SimpleKazhdanSofic.HyperbolicKazhdanHost.GeometryStart
import GroupApproximation.Manuscript.SimpleKazhdanSofic.HyperbolicKazhdanHost.GeometryNormalClosure
import GroupApproximation.Manuscript.SimpleKazhdanSofic.HyperbolicKazhdanHost.Endpoints
import GroupApproximation.Meta.AxiomGuard

/-!
# `CoulonFournierFacioGeometryStatement`, unconditionally

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.477–481 (census row
`fc84c012b409`):

> Without LEF, every countable group embeds in a finitely generated simple group~\cite{Gorjuskin,Schupp},
> and even in a simple quotient of a torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio},
> so one simple Kazhdan group contains Higman's universal finitely presented group~\cite{Higman}.

## The route

* G1 is `coulonFournierFacioGeometry_start` (`GeometryStart`): a Hull generating set on `H ∗ Γ`
  containing the letters `inr γ`, over which `inl(H)` is suitable.
* G2 is `suitable_normalClosure` (`GeometryNormalClosure`): the normal closure of a nontrivial
  element is suitable once some subgroup is.

Discharging the geometry hypothesis of the endpoints in `Endpoints` leaves the least-area
Greendlinger leaf `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` as the
only hypothesis of clause (b).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace HyperbolicKazhdanHost

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **The residual geometry of the Coulon–Fournier-Facio limit, proved.** -/
theorem coulonFournierFacioGeometry : CoulonFournierFacioGeometryStatement := by
  refine ⟨?_, ?_⟩
  · intro H Γ instH instΓ hinf htf hhyp hKT
    exact @coulonFournierFacioGeometry_start H Γ instH instΓ hinf htf hhyp hKT
  · intro Q instQ A N hN x hx
    exact @suitable_normalClosure Q instQ A N hN x hx

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.coulonFournierFacioGeometry

/-- **(b), over the least-area Greendlinger leaf alone.** -/
theorem simpleQuotientOfHyperbolicKazhdan_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    ∃ (H : Type) (_ : Group H), Infinite H ∧ Group.IsFinitelyPresented H ∧
      IsPowerTorsionFree H ∧ Hyperbolic.IsHyperbolicGroup H ∧ HasKazhdanPropertyT.{0, 0} H ∧
      ∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧
        (∃ π : H →* S, Function.Surjective π) ∧ ∃ f : Γ →* S, Function.Injective f :=
  simpleQuotientOfHyperbolicKazhdan_of_greendlinger_of_geometry hgreendlinger
    coulonFournierFacioGeometry

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.simpleQuotientOfHyperbolicKazhdan_of_greendlinger

/-- **The whole sentence of tex l.477–481, over the least-area Greendlinger leaf alone.**
Clauses (a) and (c) are closed. Clause (b) now rests only on the Greendlinger leaf. -/
theorem manuscriptSentence_withoutLEFSimpleHosts_of_greendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    (∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (G : Type) (_ : Group G), Group.FG G ∧
        IsSimpleGroup G ∧ ∃ f : Γ →* G, Function.Injective f) ∧
      (∃ (H : Type) (_ : Group H), Infinite H ∧ Group.IsFinitelyPresented H ∧
        IsPowerTorsionFree H ∧ Hyperbolic.IsHyperbolicGroup H ∧ HasKazhdanPropertyT.{0, 0} H ∧
        ∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧
          (∃ π : H →* S, Function.Surjective π) ∧ ∃ f : Γ →* S, Function.Injective f) ∧
      ∃ (G : Type) (_ : Group G), IsSimpleGroup G ∧ HasKazhdanPropertyT.{0, 0} G ∧
        ∀ (H : Type) [Group H] [Group.IsFinitelyPresented H],
          ∃ f : H →* G, Function.Injective f :=
  manuscriptSentence_withoutLEFSimpleHosts_of_greendlinger_of_geometry hgreendlinger
    coulonFournierFacioGeometry

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.manuscriptSentence_withoutLEFSimpleHosts_of_greendlinger

end HyperbolicKazhdanHost
end SimpleKazhdanSofic
end GroupApproximation
