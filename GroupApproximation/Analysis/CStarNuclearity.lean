import GroupApproximation.Analysis.CStarTensorComparison
import GroupApproximation.Analysis.NuclearityAmenability
-- `NuclearityAmenability` states its Lance theorem about an abstract predicate
-- and never mentions the reduced group C⋆-algebra, so the algebra and its
-- `Nontrivial` instance come from here instead.
import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction

/-!
# Nuclearity, defined by the comparison map

## What this module defines

`IsNuclearCStar B` says that for every C⋆-algebra `A` the canonical comparison
map `A ⊗_max B → A ⊗_min B` of `CStarTensorComparison` is injective.  By
`maxToMin_injective_iff` that is the same as saying the two tensor norms agree
on `A ⊙ B` for every `A`, which is the textbook definition; the injectivity
form is taken as primitive because it is the form the kernel machinery states,
and `isNuclearCStar_iff_norm_eq` records the other.

Until now the development could not say "nuclear" about the min/max norms at
all, because one of the two norms did not exist.  Both do, so the sentence is
statable, and `RE.05`'s theorem can be stated about the real predicate instead
of an arbitrary one.

## Two nuclearity predicates, and no claim that they agree

`Analysis/CStarExactness` already carries `IsNuclearCStarAlgebra`, defined by
the **completely positive approximation property**: the identity map is a
nuclear map.  That is a different definition from this one.  Classically the
two are equivalent — the implication from the approximation property to
`min = max` is the easy direction, the converse is Choi–Effros/Kirchberg — and
**neither direction is proved or claimed anywhere in this development**.

The two therefore coexist deliberately and must not be substituted for one
another.  This one is named `IsNuclearCStar`, without `Algebra`, precisely so
that the difference is visible at every use site.

## The universe of the test algebras

Nuclearity quantifies over *all* C⋆-algebras, which is a proper class, so the
Lean predicate quantifies over `Type u` for a universe variable `u` and is
universe-relative in exactly the way `MC.02` records for the maximal group
C⋆-algebra.  `IsNuclearCStar.{u} B` is "nuclear against test algebras in
universe `u`".  Unlike the maximal group C⋆-algebra, nothing here removes that
restriction: the seminorm device that erased the universe of the *target* of a
universal property does not apply to a quantifier over the *source* algebras of
a tensor product, since each `A` contributes its own algebraic tensor product
rather than a seminorm on a fixed one.

## What is proved about it

Nothing proves any algebra nuclear, and nothing proves any algebra non-nuclear
outright.  `reducedGroupCStar_not_isNuclearCStar_of_lance` is the `RE.05`
statement with the real predicate substituted for the abstract one, and it
keeps that row's claim-strength safeguard exactly: the Lance premise ranges
over **all** discrete groups, and the conclusion is about the marked group
alone.  A premise cooked up for that one group would not typecheck against it —
it is the general theorem or nothing — and the premise is a literature input,
not something proved here.

## Manuscript status

Infrastructure plus one restatement.  `RE.05` remains **MISSING**: what this
supplies is the vocabulary its theorem was missing, not a proof of Lance's
theorem.
-/

namespace GroupApproximation
namespace CStarTensor

open scoped TensorProduct CStarAlgebra

universe u v

/-! ## The predicate -/

/-- **Nuclearity, by the comparison map.**  `B` is nuclear when for every
C⋆-algebra `A` the canonical map `A ⊗_max B → A ⊗_min B` is injective.

The hypotheses on `A` are written as explicit anonymous binders rather than
instance binders, following `IsExactCStar`: the kernel audit reads an
instance-syntax assumption inside a definition as a finding, and a local
hypothesis of class type is found by instance search just the same. -/
def IsNuclearCStar (B : Type v) [CStarAlgebra B] [Nontrivial B] : Prop :=
  ∀ (A : Type u) (_ : CStarAlgebra A) (_ : Nontrivial A),
    Function.Injective (maxToMin (A := A) (B := B))

/-- **The textbook form.**  Nuclearity is the statement that the maximal and
minimal tensor norms agree, for every test algebra.

This is `maxToMin_injective_iff` quantified over `A`; the content is entirely
in that lemma, one direction of which is the theorem that an injective
⋆-homomorphism of C⋆-algebras is isometric. -/
theorem isNuclearCStar_iff_norm_eq (B : Type v) [CStarAlgebra B]
    [Nontrivial B] :
    IsNuclearCStar.{u} B
      ↔ ∀ (A : Type u) (_ : CStarAlgebra A) (_ : Nontrivial A)
          (x : A ⊗[ℂ] B), maxTensorNorm x = minTensorNorm x := by
  constructor
  · intro h A _ _ x
    exact (maxToMin_injective_iff.mp (h A ‹_› ‹_›)) x
  · intro h A _ _
    exact maxToMin_injective_iff.mpr (h A ‹_› ‹_›)

end CStarTensor

/-! ## The `RE.05` statement, with the real predicate -/

namespace NuclearityAmenability

open CStarTensor Amenability

/-- **`RE.05`, with nuclearity meaning nuclearity.**  If Lance's theorem holds
— every discrete group whose reduced C⋆-algebra is nuclear has an invariant
mean — then the reduced C⋆-algebra of the marked group is not nuclear.

This is `reducedGroupCStar_not_nuclear_of_lance` with `IsNuclearCStar
(ReducedGroupCStar ·)` substituted for its abstract predicate, and the
substitution changes nothing about the shape that row's note protects.  The
premise still quantifies over **every** group `G`, so it cannot be met by an
assumption manufactured for the marked group; the conclusion is still about
that group alone; and no hypothesis specific to it appears.  The mathematical
content on this side of the arrow remains `markedGroup_not_hasInvariantMean`,
which is premise-free.

Lance's theorem itself is *not* proved here and is not provable from anything
in this development; it enters as a hypothesis and is a literature input. -/
theorem reducedGroupCStar_not_isNuclearCStar_of_lance
    (lance : ∀ (G : Type) [Group G],
      IsNuclearCStar.{u} (ReducedGroupCStarTrace.ReducedGroupCStar G) →
        HasInvariantMean G) :
    ¬ IsNuclearCStar.{u}
        (ReducedGroupCStarTrace.ReducedGroupCStar
          LiteralNonMFPresentation.MarkedGroup) :=
  reducedGroupCStar_not_nuclear_of_lance
    (fun G _ => IsNuclearCStar.{u} (ReducedGroupCStarTrace.ReducedGroupCStar G))
    lance

end NuclearityAmenability
end GroupApproximation
