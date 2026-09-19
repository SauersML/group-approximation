import GroupApproximation.Monsters.UniversalFinitelyPresentedGroup
import GroupApproximation.Algebra.TorsionFreeQuotient
import GroupApproximation.Algebra.CoprodIPresentation

/-!
# Chiodo's absorber in Chiodo's own shape: the free product

`Monsters.ChiodoTorsionFreeAbsorber` builds the group that absorbs every
finitely presented torsion-free group as

    A  =  (⨁_{c : FinitePresentationCode} G_c)^tf ,

a *restricted direct product* passed to its universal torsion-free quotient,
and its docstring records why the direct sum was chosen over the free product
Chiodo actually uses (arXiv:1107.1489v4, proof of Theorem 3.9): the free
product looked as though it would need the Kurosh-type input that torsion in
a free product is conjugate into a factor, which Mathlib does not have.

**It does not need that input.**  This file builds

    A_*  =  (⨿_{c : FinitePresentationCode} G_c)^tf

and proves the same three things about it --- countable, torsion-free,
absorbs every finitely presented torsion-free group --- unconditionally, by
exactly the same two-line argument.  The reason the Kurosh input is not
needed is that the free product is never claimed to be torsion-free: the
group that has to be torsion-free is the *quotient* `A_*`, and it is
torsion-free by construction (`isPowerTorsionFree_torsionFreeQuotient`,
Chiodo's Corollary 3.4).  What has to survive the quotient is one free
factor at a time, and that is the retraction principle
(`Chiodo.injective_of_retraction`), which needs a retraction of the ambient
group onto the factor.  A free product has one, for the same formal reason a
direct sum does: `Monoid.CoprodI.lift (Pi.mulSingle c (MonoidHom.id _))` is
the identity on the `c`-th factor and kills the others.  Mathlib proves
exactly that as `Monoid.CoprodI.of_leftInverse`, and it is the only fact
about the free product this file uses.

## Why the free product is worth having anyway

Both absorbers work, and neither supersedes the other as a Lean object.  The
free product is the one Chiodo's own proof names, and it is the better input
to the step that is still owed, for a reason about *presentations* rather
than about groups.

A presentation of the direct sum on the disjoint union of the factors'
generating sets needs, besides the relators of each factor, the commutators
`[x, y]` for every pair of generators drawn from two distinct factors --- a
second, quadratic family of relators to certify recursive.  A presentation of
the free product needs no cross relators at all: it is literally

    ⟨ Σ_c X_c | ⋃_c R_c ⟩ ,

the disjoint union of the factors' generators against the disjoint union of
their relators.  Since `FinitePresentationCode` is a decidable index type and
each `(X_c, R_c)` is read off the code itself, that is the cleanest *relator
set* available for an absorbing group.

**One caveat, recorded so the record is accurate.**  Cleanest relator set does
not mean easiest recursive presentation.  `Higman.Program.RecursivePresentation`
formulates recursive presentability as *the word problem is recursively
enumerable*, and on that formulation the **direct sum is the easier input**: a
word is trivial in a restricted direct product exactly when each of its finitely
many coordinates is trivial, a finite conjunction of recursively enumerable
conditions, whereas triviality in a free product needs a search over
syllable-collapse certificates because triviality in a factor is itself only
recursively enumerable.  So `Higman.Program`'s split (B1), which is stated for
`Monsters.CodedDirectSum`, is the right one to prove; the free product's
advantage is on the relator side, not the word-problem side.

Section 4 below makes that presentation a Lean object rather than a remark:
`universalPresentation` is an isomorphism between
`PresentedGroup codedCoprodRels` and the ambient free product, where
`codedCoprodRels` is `⋃_c (blockInj c)_* R_c` and the generating type is
`Σ c, Fin c.1`.  The general theorem behind it,
`Algebra.CoprodIPresentation.coprodIPresentation`, is the indexed form of
Mathlib's binary `PresentedGroup.coprodPresentations`.  What is still prose,
and is not formalized anywhere here, is the *computability* of that relator
set and of Proposition 3.8's enlargement of it.

## What is proved, and what is not

Proved, unconditionally: `chiodoFreeAbsorber_torsionFree`,
`chiodoFreeAbsorber_countable`, `chiodoFreeEmb_injective`,
`embeds_chiodoFreeAbsorber`, `universal_of_embedding_chiodoFreeAbsorber`.

Not proved, and not attempted: that `A_*` is recursively presented (Chiodo
Proposition 3.8; this repository has no notion of recursive presentation for
infinitely generated groups), and that `A_*` embeds in a finitely presented
torsion-free group (Chiodo Theorem 2.2, the torsion-order-preserving Higman
embedding).  The second is the whole of what
`Sofic.ChiodoBelegradekTheorem` is still owed.
-/

namespace GroupApproximation
namespace Monsters

open GroupApproximation.Chiodo

/-! ## 1.  Codes present finitely presented groups

Recorded as an instance because the absorbing statement is quantified over
finitely presented groups and the coded groups have to be seen as such. -/

/-- The group of a finite presentation code is finitely presented: finitely
many generators and finitely many relators is what a code *is*. -/
instance codedPresentedGroup_finitelyPresented (c : FinitePresentationCode) :
    Group.IsFinitelyPresented (CodedPresentedGroup c) := by
  haveI : Finite (c.2 : Set (FreeGroup (Fin c.1))) :=
    Set.Finite.to_subtype (Finset.finite_toSet _)
  infer_instance

/-! ## 2.  The retraction onto a free factor -/

/-- **A free factor of an indexed free product is a retract.**

This is `Monoid.CoprodI.of_leftInverse` --- the homomorphism that is the
identity on the `c`-th factor and trivial on every other factor --- packaged
existentially so that no decidability instance escapes into the statement.
It is the only property of the free product used in this file, and it is the
exact analogue of `codedEval_codedOf` for the direct sum. -/
theorem exists_coprod_retraction (c : FinitePresentationCode) :
    ∃ r : UniversalFinitelyPresentedGroup →* CodedPresentedGroup c,
      ∀ x : CodedPresentedGroup c, r (Monoid.CoprodI.of x) = x := by
  classical
  exact
    ⟨Monoid.CoprodI.lift (Pi.mulSingle c (MonoidHom.id (CodedPresentedGroup c))),
      Monoid.CoprodI.of_leftInverse c⟩

/-! ## 3.  The absorber -/

/-- **Chiodo's absorber**, in the shape his proof of Theorem 3.9 uses: the
universal torsion-free quotient of the free product of the groups of *all*
finite presentation codes.  No filtering of the index type, and no claim that
the free product itself is torsion-free. -/
abbrev ChiodoFreeAbsorber : Type :=
  TorsionFreeQuotient UniversalFinitelyPresentedGroup

/-- The absorber is torsion-free.  Chiodo's Corollary 3.4 and nothing else;
no property of the free factors is used, and in particular the free product
is *not* claimed torsion-free. -/
theorem chiodoFreeAbsorber_torsionFree : IsPowerTorsionFree ChiodoFreeAbsorber :=
  isPowerTorsionFree_torsionFreeQuotient

instance chiodoFreeAbsorber_countable : Countable ChiodoFreeAbsorber :=
  Function.Surjective.countable toTorsionFreeQuotient_surjective

/-- The map placing one free factor into the absorber. -/
def chiodoFreeEmb (c : FinitePresentationCode) :
    CodedPresentedGroup c →* ChiodoFreeAbsorber :=
  (toTorsionFreeQuotient UniversalFinitelyPresentedGroup).comp
    (Monoid.CoprodI.of (i := c))

/-- **A torsion-free free factor survives the quotient.**  The other factors
may have as much torsion as they like: the retraction of the free product
onto this factor lands in a torsion-free group, so it kills the torsion-free
radical, so the radical meets this factor trivially. -/
theorem chiodoFreeEmb_injective (c : FinitePresentationCode)
    (hc : IsPowerTorsionFree (CodedPresentedGroup c)) :
    Function.Injective (chiodoFreeEmb c) := by
  obtain ⟨r, hr⟩ := exists_coprod_retraction c
  unfold chiodoFreeEmb
  exact injective_of_retraction hc (Monoid.CoprodI.of (i := c)) r hr

/-- **The absorbing property.**  Every finitely presented torsion-free group
embeds in the free-product absorber. -/
theorem embeds_chiodoFreeAbsorber (Q : Type) [Group Q]
    [Group.IsFinitelyPresented Q] (hQ : IsPowerTorsionFree Q) :
    ∃ f : Q →* ChiodoFreeAbsorber, Function.Injective f := by
  obtain ⟨c, ⟨e⟩⟩ := exists_mulEquiv_codedPresentedGroup Q
  have hc : IsPowerTorsionFree (CodedPresentedGroup c) :=
    IsPowerTorsionFree.comap hQ e.symm.toMonoidHom e.symm.injective
  exact ⟨(chiodoFreeEmb c).comp e.toMonoidHom,
    (chiodoFreeEmb_injective c hc).comp e.injective⟩

/-- The absorbing property in the shape the downstream reduction consumes:
any group containing the free-product absorber contains every finitely
presented torsion-free group. -/
theorem universal_of_embedding_chiodoFreeAbsorber {P : Type} [Group P]
    (g : ChiodoFreeAbsorber →* P) (hg : Function.Injective g) :
    ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
      IsPowerTorsionFree Q → ∃ f : Q →* P, Function.Injective f := by
  intro Q _ _ hQ
  obtain ⟨f, hf⟩ := embeds_chiodoFreeAbsorber Q hQ
  exact ⟨g.comp f, hg.comp hf⟩

/-- The absorber is infinite: it already contains the infinite cyclic group,
which is finitely presented and torsion-free. -/
instance chiodoFreeAbsorber_infinite : Infinite ChiodoFreeAbsorber := by
  obtain ⟨f, hf⟩ :=
    embeds_chiodoFreeAbsorber (Multiplicative ℤ)
      IsPowerTorsionFree.of_isMulTorsionFree
  exact Infinite.of_injective f hf

/-! ## 4.  The ambient free product, presented

The absorber is `(⨿_c G_c)^tf`, and the passage to `^tf` is the only step of
the construction that is not syntactic.  This section writes down the
presentation of what it is applied to. -/

/-- The generating type of the free product presentation: one generator for
each generator of each code.  Countable, because `FinitePresentationCode`
is. -/
abbrev CodedGenerator : Type := Σ c : FinitePresentationCode, Fin c.1

theorem codedGenerator_countable : Countable CodedGenerator := inferInstance

/-- The relator set of the free product: the relators of each code, pushed
into the free group on `CodedGenerator`, and **nothing else** --- no
commutators between generators of distinct codes, which is exactly what a
presentation of the restricted direct product would have had to add. -/
abbrev codedCoprodRels : Set (FreeGroup CodedGenerator) :=
  CoprodIPresentation.coprodRels
    fun c : FinitePresentationCode ↦ (c.2 : Set (FreeGroup (Fin c.1)))

/-- **The free product of all coded groups, presented.**  The generating type
is `Σ c, Fin c.1` and the relator set is the union of the codes' own relator
sets. -/
def universalPresentation :
    PresentedGroup codedCoprodRels ≃* UniversalFinitelyPresentedGroup :=
  CoprodIPresentation.coprodIPresentation
    fun c : FinitePresentationCode ↦ (c.2 : Set (FreeGroup (Fin c.1)))

/-- What the presentation does on a generator: the generator `⟨c, k⟩` goes to
the `k`-th generator of the `c`-th free factor.  Recorded so that the
identification is usable and not merely asserted. -/
theorem universalPresentation_of (x : CodedGenerator) :
    universalPresentation (PresentedGroup.of x) =
      Monoid.CoprodI.of (i := x.1)
        (PresentedGroup.of (rels := (x.1.2 : Set (FreeGroup (Fin x.1.1)))) x.2) :=
  CoprodIPresentation.coprodIPresentation_of _ x

/-- The embedding of a free factor into the absorber, unfolded: it is the
factor inclusion followed by the projection to the torsion-free quotient.
The projection is the only non-syntactic step of the construction, and it is
where Chiodo's Proposition 3.8 would supply the effective enlargement of
`codedCoprodRels`. -/
theorem chiodoFreeEmb_eq (c : FinitePresentationCode) (x : CodedPresentedGroup c) :
    chiodoFreeEmb c x =
      toTorsionFreeQuotient UniversalFinitelyPresentedGroup
        (Monoid.CoprodI.of (i := c) x) := rfl

end Monsters
end GroupApproximation
