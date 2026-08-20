import GroupApproximation.Sofic.ChiodoUniversalHost
import GroupApproximation.Monsters.ChiodoFreeProductAbsorber
import GroupApproximation.Monsters.UniversalFinitelyPresentedTorsionFreeGroup
import GroupApproximation.Algebra.ProductFinitePresentation

/-!
# Chiodo Theorem 3.10 / Belegradek Theorem A.1, as a single closed formula

> There exists a finitely presented torsion-free group containing a copy of
> every finitely presented torsion-free group.

Chiodo, arXiv:1107.1489v4, Theorem 3.10, which Chiodo credits to Theorem A.1
of Belegradek's appendix to Belegradek--Szczepanski.  The statement is used
by Fournier-Facio, arXiv:2608.02025 §2, as the first of the two inputs of
`KC.21`, and this repository carries it as
`FournierFacioUniversal.UniversalTorsionFreeHost`.

This file writes the sentence down as one closed formula,
`ChiodoBelegradek.Statement`, and separates what is proved from what is not.

## The three clauses, and which one is missing

The statement asks a single group `U` to satisfy three clauses: *finitely
presented*, *torsion-free*, *contains every finitely presented torsion-free
group*.  **Two of the three are already inhabited unconditionally in this
repository, jointly and by an explicit group**, and this file records that
as a theorem:

    statementCountable :  ∃ U, Countable U ∧ torsion-free U ∧ universal U

is *proved*, with `U := Monsters.ChiodoFreeAbsorber` (equally with
`Monsters.ChiodoAbsorber`).  So the whole distance between what is proved and
what Chiodo Theorem 3.10 asserts is the replacement of `Countable U` by
`Group.IsFinitelyPresented U`, on a group that already exists and is already
known to be torsion-free and already known to be universal.

That replacement is Higman's embedding theorem in Chiodo's torsion-order
preserving form (his Theorem 2.2), and it is **not** proved here, in
`Sofic.ChiodoUniversalHost`, in this repository, or in Mathlib.  It is not a
bookkeeping step: an `n`-generated finitely presented group has a recursively
enumerable word problem, so a group containing every finitely presented
torsion-free group --- among them ones with unsolvable word problem --- can
only be produced by a construction that simulates a machine inside a group.
Nothing below pretends otherwise, and every declaration that concludes
`Statement` takes the missing embedding as an explicit argument.

## What is proved here, unconditionally

* `ContainsEveryFPTorsionFree` --- the third clause as a named predicate,
  definitionally equal to the inline `∀`-form the rest of the repository
  uses (`containsEveryFPTorsionFree_iff_inline`, `Iff.rfl`), so no statement
  is changed by naming it.
* `ContainsEveryFPTorsionFree.comp` --- universality transfers along an
  injective homomorphism.  (This is `FournierFacioUniversal.universal_comp`
  restated at the named predicate, proved again rather than transported, so
  that the two forms cannot drift apart.)
* `containsEveryFPTorsionFree_iff_codes` --- **the class quantifier is a
  countable conjunction.**  Universality, stated over every finitely
  presented torsion-free *type*, is equivalent to universality over the
  countable type `Monsters.TorsionFreePresentationCode` of finite
  presentation codes whose group is torsion-free.  This is the fact that
  makes an absorbing group possible at all, and it is the only place the
  coding of presentations is used.
* `containsEveryFPTorsionFree_chiodoFreeAbsorber` and
  `containsEveryFPTorsionFree_chiodoAbsorber` --- both explicit absorbers
  satisfy the third clause.
* `statementCountable` --- the countable form of Theorem 3.10, proved.
* `statementCountable_of_statement` --- and it really is a *weakening*:
  a finitely presented group is countable
  (`countable_of_isFinitelyPresented`), so `Statement` implies the sentence
  that is proved.  The two differ in exactly one clause and in nothing else.
* `witness_prod` --- the *"in particular `P₁ × P₂`"* of Fournier-Facio's
  remark: a witness squared is again a witness.  Finite presentation of the
  product is `ProductFinitePresentation.instProd`, torsion-freeness is
  `IsPowerTorsionFree.prod`, universality is `comp` along `u ↦ (u, 1)`.
* `Statement`'s consequences: a witness is infinite, contains a free group of
  every finite rank, and every two witnesses embed in each other.

## What produces `Statement`, and nothing here inhabits any of it

Four producers, in decreasing order of how much they assume:

* `statement_of_host` --- from `UniversalTorsionFreeHost`, the packaged
  citation.  Nothing inhabits it.
* `statement_of_hull` / `statement_of_freeHull` --- from
  `ChiodoHost.TorsionFreeHigmanHull` at either absorber, i.e. from Chiodo's
  Theorem 2.2 applied once.  Nothing inhabits it.
* `statement_of_embedding_chiodoFreeAbsorber` and
  `statement_of_embedding_chiodoAbsorber` --- **the sharpest form of what is
  owed**, with no structure at all: a finitely presented torsion-free group
  and an injection of one named, explicitly constructed countable group into
  it.  Every hypothesis is a bare formula, so a reader who obtains such an
  embedding from anywhere discharges Theorem 3.10 outright.

Following `Sofic.FournierFacioUniversalGroup`, no declaration here concludes
an *input structure* from bare formulas, and no statement here is an `↔`
between an input name and a formula: the corpus audit must keep reporting the
Higman input as open, and it does.
-/

namespace GroupApproximation
namespace ChiodoBelegradek

open GroupApproximation.Monsters

/-! ## 1.  The third clause, named -/

/-- **`U` contains a copy of every finitely presented torsion-free group.**

This is the third clause of Chiodo Theorem 3.10, and it is the predicate the
whole lane is about.  It is *definitionally* the inline `∀`-form used in
`Sofic.FournierFacioUniversalGroup` and `Sofic.ChiodoUniversalHost`; see
`containsEveryFPTorsionFree_iff_inline`. -/
def ContainsEveryFPTorsionFree (U : Type) [Group U] : Prop :=
  ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
    IsPowerTorsionFree Q → ∃ f : Q →* U, Function.Injective f

/-- Naming the predicate changes no statement: it is the inline form, on the
nose. -/
theorem containsEveryFPTorsionFree_iff_inline (U : Type) [Group U] :
    ContainsEveryFPTorsionFree U ↔
      ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
        IsPowerTorsionFree Q → ∃ f : Q →* U, Function.Injective f :=
  Iff.rfl

/-- Introduction rule, so that consumers never have to unfold the definition. -/
theorem containsEveryFPTorsionFree_of (U : Type) [Group U]
    (h : ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
      IsPowerTorsionFree Q → ∃ f : Q →* U, Function.Injective f) :
    ContainsEveryFPTorsionFree U := h

/-- Elimination rule. -/
theorem ContainsEveryFPTorsionFree.embeds {U : Type} [Group U]
    (h : ContainsEveryFPTorsionFree U) (Q : Type) [Group Q]
    [Group.IsFinitelyPresented Q] (hQ : IsPowerTorsionFree Q) :
    ∃ f : Q →* U, Function.Injective f :=
  h Q hQ

/-- **Universality transfers along an embedding.**  Nothing is assumed about
the larger group --- not finite presentation, not torsion-freeness --- which
is why the three clauses of Theorem 3.10 are independent of one another. -/
theorem ContainsEveryFPTorsionFree.comp {U P : Type} [Group U] [Group P]
    (hU : ContainsEveryFPTorsionFree U) (g : U →* P) (hg : Function.Injective g) :
    ContainsEveryFPTorsionFree P := by
  refine containsEveryFPTorsionFree_of P ?_
  intro Q _ _ hQ
  obtain ⟨f, hf⟩ := hU.embeds Q hQ
  exact ⟨g.comp f, hg.comp hf⟩

/-! ## 2.  The class quantifier is a countable conjunction -/

/-- **Universality is a countable conjunction.**

`ContainsEveryFPTorsionFree` quantifies over every finitely presented
torsion-free *type*; this says it is equivalent to a statement indexed by the
countable type `Monsters.TorsionFreePresentationCode`.  Forward is the
instance `Monsters.codedPresentedGroup_finitelyPresented` --- a code presents
a finitely presented group --- together with the code's own torsion-freeness
proof; backward is `Monsters.exists_mulEquiv_codedPresentedGroup`, that every
finitely presented group *is* a coded one up to isomorphism.

This is the fact that makes an absorbing group possible: a countable
conjunction of embedding demands can be met by one countable group. -/
theorem containsEveryFPTorsionFree_iff_codes {U : Type} [Group U] :
    ContainsEveryFPTorsionFree U ↔
      ∀ c : TorsionFreePresentationCode,
        ∃ f : TorsionFreeCodedGroup c →* U, Function.Injective f := by
  constructor
  · intro h c
    exact h.embeds (TorsionFreeCodedGroup c) c.2
  · intro h
    refine containsEveryFPTorsionFree_of U ?_
    intro Q _ _ hQ
    obtain ⟨c, ⟨e⟩⟩ := exists_mulEquiv_codedPresentedGroup Q
    have hc : IsPowerTorsionFree (CodedPresentedGroup c) :=
      IsPowerTorsionFree.comap hQ e.symm.toMonoidHom e.symm.injective
    obtain ⟨f, hf⟩ := h ⟨c, hc⟩
    exact ⟨f.comp e.toMonoidHom, hf.comp e.injective⟩

/-! ## 3.  Both explicit absorbers satisfy the third clause -/

/-- Chiodo's absorber in his own free-product shape is universal. -/
theorem containsEveryFPTorsionFree_chiodoFreeAbsorber :
    ContainsEveryFPTorsionFree ChiodoFreeAbsorber :=
  containsEveryFPTorsionFree_of _ fun Q _ _ hQ => embeds_chiodoFreeAbsorber Q hQ

/-- The direct-sum absorber is universal. -/
theorem containsEveryFPTorsionFree_chiodoAbsorber :
    ContainsEveryFPTorsionFree ChiodoAbsorber :=
  containsEveryFPTorsionFree_of _ fun Q _ _ hQ => embeds_chiodoAbsorber Q hQ

/-! ## 4.  The statement, and the countable form of it that is proved -/

/-- **Chiodo Theorem 3.10 = Belegradek Theorem A.1**, as a closed formula:
there is a finitely presented torsion-free group containing a copy of every
finitely presented torsion-free group.

Nothing in this repository proves this.  Section 6 lists exactly what would. -/
def Statement : Prop :=
  ∃ (U : Type) (_ : Group U),
    Group.IsFinitelyPresented U ∧ IsPowerTorsionFree U ∧
      ContainsEveryFPTorsionFree U

/-- The same sentence with *finitely presented* weakened to *countable*.
This is what separates the proved from the unproved: the two statements
differ in one clause, on a group that is already built. -/
def StatementCountable : Prop :=
  ∃ (U : Type) (_ : Group U),
    Countable U ∧ IsPowerTorsionFree U ∧ ContainsEveryFPTorsionFree U

/-- **The countable form of Theorem 3.10, proved unconditionally**, with
Chiodo's own free product as the witness.

Read against `Statement`, this is a precise statement of the remaining gap:
torsion-freeness and universality are settled, and the single clause left to
supply is finite presentation. -/
theorem statementCountable : StatementCountable :=
  ⟨ChiodoFreeAbsorber, inferInstance, inferInstance,
    chiodoFreeAbsorber_torsionFree, containsEveryFPTorsionFree_chiodoFreeAbsorber⟩

/-- The same, with the direct-sum absorber, so that neither construction is
load-bearing on its own. -/
theorem statementCountable' : StatementCountable :=
  ⟨ChiodoAbsorber, inferInstance, inferInstance,
    chiodoAbsorber_torsionFree, containsEveryFPTorsionFree_chiodoAbsorber⟩

/-- A finitely presented group is countable: it is a quotient of a free group
on finitely many generators. -/
theorem countable_of_isFinitelyPresented (U : Type) [Group U]
    [h : Group.IsFinitelyPresented U] : Countable U := by
  obtain ⟨n, φ, hφ, -⟩ := h.out
  exact hφ.countable

/-- **`StatementCountable` is a weakening of `Statement`.**  The two sentences
differ in exactly the clause named and in nothing else, so the theorem proved
above really is the whole of Theorem 3.10 minus finite presentation. -/
theorem statementCountable_of_statement (h : Statement) : StatementCountable := by
  obtain ⟨U, inst, hfp, htf, huniv⟩ := h
  haveI := inst
  haveI := hfp
  exact ⟨U, inst, countable_of_isFinitelyPresented U, htf, huniv⟩

/-! ## 5.  What a witness would give -/

/-- **A witness squared is a witness.**  This is the *"in particular a direct
product `P₁ × P₂` with `Pᵢ ≅ P`"* of Fournier-Facio's remark, at the level of
Theorem 3.10 rather than of the Kazhdan envelope. -/
theorem witness_prod {U : Type} [Group U] [Group.IsFinitelyPresented U]
    (htf : IsPowerTorsionFree U) (huniv : ContainsEveryFPTorsionFree U) :
    Group.IsFinitelyPresented (U × U) ∧ IsPowerTorsionFree (U × U) ∧
      ContainsEveryFPTorsionFree (U × U) := by
  refine ⟨inferInstance, IsPowerTorsionFree.prod htf htf, ?_⟩
  refine huniv.comp ((MonoidHom.id U).prod (1 : U →* U)) ?_
  intro a b hab
  simpa using congrArg Prod.fst hab

/-- A universal group is infinite: it contains the infinite cyclic group,
which is finitely presented and torsion-free. -/
theorem infinite_of_containsEvery {U : Type} [Group U]
    (huniv : ContainsEveryFPTorsionFree U) : Infinite U := by
  obtain ⟨f, hf⟩ :=
    huniv.embeds (Multiplicative ℤ) IsPowerTorsionFree.of_isMulTorsionFree
  exact Infinite.of_injective f hf

/-- A universal group contains a free group of every finite rank. -/
theorem embeds_freeGroup_of_containsEvery {U : Type} [Group U]
    (huniv : ContainsEveryFPTorsionFree U) (m : ℕ) :
    ∃ f : FreeGroup (Fin m) →* U, Function.Injective f :=
  huniv.embeds (FreeGroup (Fin m)) IsPowerTorsionFree.of_isMulTorsionFree

/-- **Any two witnesses embed in each other.**  A universal group is therefore
unique up to mutual embedding, which is all Theorem 3.10 asserts about it. -/
theorem embeds_of_containsEvery {U V : Type} [Group U] [Group V]
    [Group.IsFinitelyPresented U] (hU : IsPowerTorsionFree U)
    (hV : ContainsEveryFPTorsionFree V) :
    ∃ f : U →* V, Function.Injective f :=
  hV.embeds U hU

/-! ## 6.  What would produce `Statement`

Every declaration in this section takes the missing input as an explicit
argument.  None of them is applied to anything, here or anywhere else in the
repository. -/

/-- From the packaged citation.  `UniversalTorsionFreeHost` is Chiodo Theorem
3.10 itself, carried as a structure; nothing inhabits it. -/
theorem statement_of_host
    (H : FournierFacioUniversal.UniversalTorsionFreeHost) : Statement := by
  refine ⟨H.Carrier, H.groupCarrier, H.finitelyPresentedCarrier, H.torsionFree, ?_⟩
  exact containsEveryFPTorsionFree_of _ H.universal

/-- From Chiodo's Theorem 2.2 applied once, to the direct-sum absorber. -/
theorem statement_of_hull
    (H : ChiodoHost.TorsionFreeHigmanHull ChiodoAbsorber) : Statement := by
  refine ⟨H.Carrier, H.groupCarrier, H.finitelyPresentedCarrier, H.torsionFree, ?_⟩
  exact containsEveryFPTorsionFree_chiodoAbsorber.comp H.emb H.emb_injective

/-- From Chiodo's Theorem 2.2 applied once, to the free-product absorber ---
the group Chiodo's own proof of Theorem 3.9 names. -/
theorem statement_of_freeHull
    (H : ChiodoHost.TorsionFreeHigmanHull ChiodoFreeAbsorber) : Statement := by
  refine ⟨H.Carrier, H.groupCarrier, H.finitelyPresentedCarrier, H.torsionFree, ?_⟩
  exact containsEveryFPTorsionFree_chiodoFreeAbsorber.comp H.emb H.emb_injective

/-- **The sharpest form of what Theorem 3.10 is owed.**  No structure, no
quantification over finitely presented groups: one finitely presented
torsion-free group, and one injection into it of one named countable group
that this repository constructs.

Anyone with such an embedding has Theorem 3.10. -/
theorem statement_of_embedding_chiodoFreeAbsorber {U : Type} [Group U]
    [Group.IsFinitelyPresented U] (hU : IsPowerTorsionFree U)
    (g : ChiodoFreeAbsorber →* U) (hg : Function.Injective g) : Statement := by
  refine ⟨U, inferInstance, inferInstance, hU, ?_⟩
  exact containsEveryFPTorsionFree_chiodoFreeAbsorber.comp g hg

/-- The same, for the direct-sum absorber. -/
theorem statement_of_embedding_chiodoAbsorber {U : Type} [Group U]
    [Group.IsFinitelyPresented U] (hU : IsPowerTorsionFree U)
    (g : ChiodoAbsorber →* U) (hg : Function.Injective g) : Statement := by
  refine ⟨U, inferInstance, inferInstance, hU, ?_⟩
  exact containsEveryFPTorsionFree_chiodoAbsorber.comp g hg

end ChiodoBelegradek
end GroupApproximation
