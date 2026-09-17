import GroupApproximation.Manuscript.NonMF.RelatedTWW.Definitions
import GroupApproximation.Analysis.UniversalCoefficientTheorem
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Tikuisis--White--Winter): what the parameter `T` does

Census row `82cac0c03a39`, `non_mf_groups_exist.tex` L315--318:

> for algebras that satisfy the universal coefficient theorem and have a
> faithful trace, the theorem of Tikuisis, White, and Winter recalled above
> answers this~\cite{TWW}.

`RelatedTWW.Definitions` reads "satisfies the universal coefficient theorem" as
`T.SatisfiesUCT S` for a Kasparov theory `T : KK.KasparovTheory`. That
structure only records the axioms the corpus consumes: an associative unital
product, functorial homotopy-invariant classes of `⋆`-homomorphisms, and an
abelian group structure on each `KK`-group, with no link between the two.
This module checks what the parameter does to the named gap
`TikuisisWhiteWinterStatement T`.

## Findings, all proved below

* The axioms have a **degenerate model**, `trivialKasparovTheory`, with every
  `KK`-group equal to `PUnit`. In it any two algebras are `KK`-equivalent
  (`trivialKasparovTheory_kkEquivalent`), so every separable algebra satisfies
  the UCT (`satisfiesUCT_trivialKasparovTheory`).
* So `T` cannot be chosen to make the gap vacuously true. Commutative algebras
  satisfy the UCT at every `T`, because `KK`-equivalence is reflexive. The
  degenerate choice goes the other way: at `trivialKasparovTheory` the gap is
  the theorem **without** its UCT hypothesis
  (`tikuisisWhiteWinterStatement_trivialKasparovTheory_iff`).
* Hence the gap at **every** `T` is equivalent to "every faithful tracial state
  on a separable nuclear C⋆-algebra is quasidiagonal"
  (`forall_tikuisisWhiteWinterStatement_iff`). That is an open problem, not
  the Annals theorem. Likewise the restricted answer at the degenerate `T` is
  the Blackadar--Kirchberg question on all separable nuclear algebras with a
  faithful trace (`blackadarKirchbergAnswer_trivialKasparovTheory_iff`).

Consequence for the row: an endpoint of the shape
`∀ T, BlackadarKirchbergQuasidiagonalAnswerUCTFaithfulTrace T` would prove more
than the printed sentence, and more than is currently known. The printed
sentence is about Kasparov's `KK`, and the corpus constructs no model of it.

Statements are at universe `0`, where the corpus has the commutative object
`KK.complexAlgebra`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedTWW

noncomputable section

universe u

/-! ## The degenerate Kasparov theory -/

/-- **The degenerate model of the `KK.KasparovTheory` axioms**: every `KK`-group
is `PUnit`. Every axiom holds, because both sides of each equation lie in
`PUnit`. -/
def trivialKasparovTheory : KK.KasparovTheory.{u} where
  Grp _ _ := PUnit.{u + 1}
  product _ _ := PUnit.unit
  product_assoc _ _ _ := rfl
  unit _ := PUnit.unit
  unit_product _ := rfl
  product_unit _ := rfl
  classOf _ := PUnit.unit
  classOf_id _ := rfl
  classOf_comp _ _ := rfl
  classOf_homotopic _ := rfl
  addCommGroup _ _ := PUnit.addCommGroup

/-- In the degenerate model any two separable algebras are `KK`-equivalent. -/
theorem trivialKasparovTheory_kkEquivalent (A B : KK.SepCStarAlgebra.{u}) :
    trivialKasparovTheory.{u}.KKEquivalent A B :=
  ⟨PUnit.unit, PUnit.unit, rfl, rfl⟩

/-- In the degenerate model every separable algebra satisfies the UCT: it is
`KK`-equivalent to the commutative algebra `ℂ`. -/
theorem satisfiesUCT_trivialKasparovTheory (S : KK.SepCStarAlgebra.{0}) :
    trivialKasparovTheory.{0}.SatisfiesUCT S :=
  ⟨KK.complexAlgebra, KK.complexAlgebra_isCommutative,
    trivialKasparovTheory_kkEquivalent S KK.complexAlgebra⟩

/-! ## The gap at the degenerate model -/

/-- **At the degenerate model the gap loses its UCT hypothesis.** It says that
every faithful tracial state on a separable nuclear C⋆-algebra is
quasidiagonal. -/
theorem tikuisisWhiteWinterStatement_trivialKasparovTheory_iff :
    TikuisisWhiteWinterStatement trivialKasparovTheory.{0} ↔
      ∀ S : KK.SepCStarAlgebra.{0}, CStarExactness.IsNuclearCStarAlgebra S →
        ∀ τ : FaithfulTracialState S,
          Quasidiagonal.IsQuasidiagonalTrace (fun a : S ↦ τ a) :=
  ⟨fun h S hnuc τ ↦ h S hnuc (satisfiesUCT_trivialKasparovTheory S) τ,
    fun h S hnuc _ τ ↦ h S hnuc τ⟩

/-- **The gap at every Kasparov theory is the UCT-free statement.** The degenerate
model gives one direction; dropping the UCT hypothesis gives the other. -/
theorem forall_tikuisisWhiteWinterStatement_iff :
    (∀ T : KK.KasparovTheory.{0}, TikuisisWhiteWinterStatement T) ↔
      ∀ S : KK.SepCStarAlgebra.{0}, CStarExactness.IsNuclearCStarAlgebra S →
        ∀ τ : FaithfulTracialState S,
          Quasidiagonal.IsQuasidiagonalTrace (fun a : S ↦ τ a) :=
  ⟨fun h ↦ tikuisisWhiteWinterStatement_trivialKasparovTheory_iff.mp
      (h trivialKasparovTheory.{0}),
    fun h _ S hnuc _ τ ↦ h S hnuc τ⟩

/-- **The restricted answer at the degenerate model** is the Blackadar--Kirchberg
question on every separable nuclear stably finite algebra with a faithful
trace. -/
theorem blackadarKirchbergAnswer_trivialKasparovTheory_iff :
    BlackadarKirchbergQuasidiagonalAnswerUCTFaithfulTrace trivialKasparovTheory.{0} ↔
      ∀ S : KK.SepCStarAlgebra.{0}, CStarExactness.IsNuclearCStarAlgebra S →
        IsStablyFiniteCStarAlgebra S → Nonempty (FaithfulTracialState S) →
          IsQuasidiagonalCStarAlgebra S :=
  ⟨fun h S hnuc hsf hτ ↦ h S hnuc hsf (satisfiesUCT_trivialKasparovTheory S) hτ,
    fun h S hnuc hsf _ hτ ↦ h S hnuc hsf hτ⟩

end

end RelatedTWW
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.RelatedTWW

#audit_axioms trivialKasparovTheory_kkEquivalent
#audit_axioms satisfiesUCT_trivialKasparovTheory
#audit_axioms tikuisisWhiteWinterStatement_trivialKasparovTheory_iff
#audit_axioms forall_tikuisisWhiteWinterStatement_iff
#audit_axioms blackadarKirchbergAnswer_trivialKasparovTheory_iff
