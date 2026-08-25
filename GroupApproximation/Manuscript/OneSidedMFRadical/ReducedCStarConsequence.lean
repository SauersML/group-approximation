import GroupApproximation.Analysis.ReducedGroupCStarMFAlgebra
import GroupApproximation.Analysis.ReducedGroupCStarStablyFinite
import GroupApproximation.Manuscript.OneSidedMFRadical.HeadlineTheorem

/-!
# The reduced-C⋆ clause of `thm:headline`, and the Blackadar--Kirchberg MF question

`non_mf_groups_exist.tex`, abstract and Theorem `thm:headline` — "Its reduced
group C*-algebra `C*_r(H)` is separable and stably finite, but is not MF." —
together with the general step the Introduction states just before it: "For
every countable group `G`, the reduced group algebra `C*_r(G)` is separable and
has a faithful canonical trace, hence is stably finite.  If `C*_r(G)` is MF,
restricting an MF embedding to its canonical group unitaries shows that `G` is
MF.  Therefore a non-MF group automatically gives a separable stably finite
reduced group `C*`-algebra that is not MF."

Everything below is that general step applied at the manuscript's own group

`H = EL₁₂(L_{𝔽₂}(1,2))`,

whose failure of MF-ness is the last conjunct of
`HeadlineTheorem.manuscriptBinaryLeavittFullRadical`.  No analysis is done
here: separability is
`ReducedGroupCStarTrace.reducedGroupCStar_separableSpace`, stable finiteness is
`reducedGroupCStar_isStablyFiniteCStarAlgebra`, the unitary restriction is
`not_isMFAlgebra_reducedGroupCStar`, and the three are already packaged as
`reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra`.  What this module
adds is the *shape*: three named propositions, each with every quantifier
inside the statement, so that a reader can `#check` one name against one
printed sentence.

* `ReducedCStarConsequence` — the printed clause at `H` itself.
* `SeparableStablyFiniteNonMFCStarAlgebraExists` — the same content with the
  group forgotten: some separable stably finite C⋆-algebra is not MF.
* `NotEverySeparableStablyFiniteCStarAlgebraIsMF` — the same sentence written
  as the refutation of the universal statement it denies.

## Which Blackadar--Kirchberg question this answers, and which it does not

The manuscript's "Relation to prior work" subsection distinguishes two
questions, and so does this module.

* **The 1994 Oberwolfach suggestion is untouched.**  Blackadar and Kirchberg
  suggested there that every separable **nuclear** stably finite C⋆-algebra
  might be NF.  `C*_r(H)` is the reduced group C⋆-algebra of a non-amenable
  group — `H` has property `(T)` and is infinite, since a finite group embeds
  in a single matrix algebra and is therefore MF, whereas `H` is not — so by
  Lance's theorem it is not nuclear.  That non-nuclearity is *not* formalized
  in this repository and is *not* used anywhere below; it is recorded only to
  make the scope explicit.  Nothing in this module asserts, uses, or bears on
  the nuclear question, and none of the three propositions below should be
  read as touching it.
* **The broader MF question is the one answered.**  Their 1997 paper
  introduced MF C⋆-algebras and observed that no separable stably finite
  C⋆-algebra was known not to be MF; the question whether every separable
  stably finite C⋆-algebra is MF became known as the Blackadar--Kirchberg MF
  problem.  `NotEverySeparableStablyFiniteCStarAlgebraIsMF` is exactly the
  negation of that universal statement, at the repository's reading of the
  predicates (`Analysis.MFAlgebra.IsMFAlgebra` and
  `Analysis.ReducedGroupCStarStablyFinite.IsStablyFiniteCStarAlgebra`).

## No priority is claimed for the bare existence statement

Separable stably finite C⋆-algebras that are not MF are already known: the
negative solution of the Connes embedding problem produced them in general.
`SeparableStablyFiniteNonMFCStarAlgebraExists` is therefore *not* offered as a
new theorem, and the manuscript does not present it as one — it is stated here
only because it is the literal existential form of the printed sentence, and
because it is the shape the Blackadar--Kirchberg question is asked in.  What is
new in `thm:headline` is that such an example occurs among **reduced group**
C⋆-algebras, which is `ReducedCStarConsequence`, and that is the proposition
carrying the content.

## What "stably finite" means here

`IsStablyFiniteCStarAlgebra` is the operator-algebraic reading — every isometry
in every finite matrix amplification is a unitary — and deliberately not
mathlib's `IsStablyFiniteRing`.  The two are equivalent for C⋆-algebras by a
polar-decomposition argument that this repository does not formalize; see the
docstring of `IsStablyFiniteCStarAlgebra` itself.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open RankTwelveEndpoint
open ReducedGroupCStarTrace

/-- `H = EL₁₂(L_{𝔽₂}(1,2))` is countable.  The instance is needed both to
*state* `IsCDEOperatorMF H` and to feed the countability hypothesis of
`reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra`; `HeadlineTheorem`
declares the same instance locally, and a `local instance` is not exported to
importing modules. -/
local instance reducedCStarCountable : Countable H :=
  RankTwelveEndpoint.countable

/-! ## The printed clause at the manuscript's group -/

/-- **The printed reduced-C⋆ clause of `thm:headline`, as one proposition.**
The concrete reduced group C⋆-algebra of `H = EL₁₂(L_{𝔽₂}(1,2))` is separable,
is stably finite, and is not an MF C⋆-algebra.

The first two conjuncts hold for every countable group and use nothing about
`H`; only the third uses the failure of MF-ness proved in `HeadlineTheorem`. -/
def ReducedCStarConsequence : Prop :=
  TopologicalSpace.SeparableSpace (ReducedGroupCStar H) ∧
    IsStablyFiniteCStarAlgebra (ReducedGroupCStar H) ∧
      ¬ IsMFAlgebra (ReducedGroupCStar H)

/-- **The printed clause, proved, hypothesis-free.**  The single input about
`H` is the last conjunct of `manuscriptBinaryLeavittFullRadical`, namely
`¬ IsCDEOperatorMF H`; the rest is the general countable-group statement
`reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra`.

The printed simplicity clause of `thm:headline` is used nowhere on this
route. -/
theorem manuscriptReducedCStarConsequence : ReducedCStarConsequence := by
  obtain ⟨-, -, -, -, -, -, hnot⟩ := manuscriptBinaryLeavittFullRadical
  exact reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra H hnot

/-! ## The same content with the group forgotten -/

/-- **Existence form: some separable stably finite C⋆-algebra is not MF.**

This is the shape in which the Blackadar--Kirchberg MF question is asked, and
it is deliberately weaker than `ReducedCStarConsequence`: it forgets that the
witness is a reduced group C⋆-algebra.  As the module docstring records, the
bare existence statement is not new — the negative solution of the Connes
embedding problem already supplies such algebras — and no priority is claimed
for it here.

The `CStarAlgebra` structure is bound existentially rather than left to
instance synthesis, since `A` is a bound variable; `letI` then makes it
available to the three conjuncts, which all need it. -/
def SeparableStablyFiniteNonMFCStarAlgebraExists : Prop :=
  ∃ (A : Type) (inst : CStarAlgebra A),
    letI : CStarAlgebra A := inst
    TopologicalSpace.SeparableSpace A ∧
      IsStablyFiniteCStarAlgebra A ∧ ¬ IsMFAlgebra A

/-- **The existence statement, proved.**  The witness is `C*_r(H)` with its
canonical C⋆-algebra structure `reducedGroupCStarCStarAlgebra`, and the three
conjuncts are exactly `manuscriptReducedCStarConsequence`. -/
theorem manuscriptSeparableStablyFiniteNonMFCStarAlgebraExists :
    SeparableStablyFiniteNonMFCStarAlgebraExists :=
  ⟨ReducedGroupCStar H, inferInstance, manuscriptReducedCStarConsequence⟩

/-- **Refutation form: the Blackadar--Kirchberg MF question, answered no.**  It
is not the case that every separable stably finite C⋆-algebra is MF.

This is the negation of the universal statement recorded in the manuscript's
"Relation to prior work" subsection as the Blackadar--Kirchberg MF problem.  It
carries no nuclearity hypothesis, and correspondingly says nothing about the
1994 Oberwolfach suggestion, which did carry one. -/
def NotEverySeparableStablyFiniteCStarAlgebraIsMF : Prop :=
  ¬ ∀ (A : Type) [CStarAlgebra A],
      TopologicalSpace.SeparableSpace A → IsStablyFiniteCStarAlgebra A →
        IsMFAlgebra A

/-- **The universal statement is false.**  Instantiating it at `C*_r(H)`, whose
separability and stable finiteness are the first two conjuncts of
`manuscriptReducedCStarConsequence`, contradicts its third. -/
theorem manuscriptNotEverySeparableStablyFiniteCStarAlgebraIsMF :
    NotEverySeparableStablyFiniteCStarAlgebraIsMF := by
  intro hall
  obtain ⟨hsep, hsf, hnot⟩ := manuscriptReducedCStarConsequence
  exact hnot (hall (ReducedGroupCStar H) hsep hsf)

end OneSidedMFRadical
end Manuscript
end GroupApproximation
