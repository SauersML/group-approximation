import GroupApproximation.GGT.DGOProposition435FiniteLetters
import GroupApproximation.GGT.DGOProposition435IsolatedWitness

/-!
# The nested form of Proposition 4.35 over a finite auxiliary family

`DGOProposition435InclusionStatement` quantifies over every auxiliary index
type.  Its consumer, the joint-family selection of Hull's Lemma 4.4, only
applies it to finitely many auxiliary subgroups whose relative base is closed
under inversion.  Over such a family the local finiteness half of the joint
embedding follows from Proposition 4.14 together with the isolated-witness
statement, which `DGOProposition435IsolatedWitness` proves.  So the finite
form below has exactly one residue, the hyperbolicity of the joint relative
Cayley graph.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry

universe u v w

/-- **The nested form of Proposition 4.35 over a finite auxiliary family**
whose relative base is closed under inversion. -/
def DGOProposition435InclusionFiniteStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type v} {I : Type w} [Finite I]
    (D : RelGenSet G Lambda) (E : RelGenSet G I),
      D.alphabet.carrier ⊆ E.base →
      OsinComponents.DGO421BaseSymmetric E →
      D.IsHyperbolicallyEmbedded →
      E.IsHyperbolicallyEmbedded →
        (jointRelGenSet D E).IsHyperbolicallyEmbedded

/-- The universal nested form gives the finite one. -/
theorem dgoProposition435InclusionFiniteStatement_of_inclusionStatement
    (h : DGOProposition435InclusionStatement.{u, v, w}) :
    DGOProposition435InclusionFiniteStatement.{u, v, w} := by
  intro G _ Lambda I _ D E hbase _ hD hE
  exact h D E hbase hD hE

/-- **The finite nested form from joint hyperbolicity and Proposition 4.14.**
The isolated-witness statement is a theorem, so the local finiteness of the
original peripheral metrics in the joint alphabet comes from Proposition 4.14,
and only the hyperbolicity of the joint relative Cayley graph is taken as
input. -/
theorem dgoProposition435InclusionFiniteStatement_of_jointHyperbolic
    (hhyp : DGOProposition435JointHyperbolicStatement.{u, v, w})
    (h414 : OsinComponents.DGOProposition414Uniform.{u, w}) :
    DGOProposition435InclusionFiniteStatement.{u, v, w} := by
  intro G _ Lambda I _ D E hbase hEsymm hD hE
  exact isHyperbolicallyEmbedded_jointRelGenSet_of_proposition414Uniform h414
    dgoProposition435IsolatedWitness D E hbase hEsymm hD hE
    (hhyp D E hbase hD hE)

end RelHyp
end GGT
end GroupApproximation
