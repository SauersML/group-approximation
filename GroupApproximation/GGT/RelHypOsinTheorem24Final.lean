import GroupApproximation.GGT.RelHypOsinTheorem24Repaired

/-!
# The final weighted leaves: Osin's quantifier order restored

## RETIRED from hypothesis position (issue #52), and not the last generation

Two corrections to the paragraph below.  It was not the last generation -- a
fourth followed, at the relative Cayley graph
(`GGT/RelHypOsin24CayleyLeaf.lean`) -- and `OsinTheorem24Final` is refuted, by
`GGT/RelHypOsin24Collapse.not_weightedGreendlingerLeafFinal_universal`.

The quantifier diagnosis below is half right and worth keeping: the length floor
`ρ` did have to move inside.  What it missed is that the *small-cancellation
constant* moves too.  Osin's Lemma 5.1 reads `∀ λ, c, N. ∃ µ, ε, ρ. ∀ R`, and
his Lemma 4.4 restricts `µ ∈ (0, 1/16]` -- note that Osin's `λ` is the
quasi-geodesic constant and his `µ` is the small-cancellation constant, which is
the `lam` of this file.  Here `lam` is still universally quantified, and it is
spent at `1/7` against designs certified at `C'(1/8)`; both exceed `1/16`.

None of that is repaired by a fifth generation, because the machinery was never
the citation: **Osin's Theorem 2.4 has no small-cancellation hypothesis at
all**.  See `GGT/RelHypOsinTheorem24.lean` for the explanation and
`GGT/RelHypFournierFacioProp23.lean` for the route that replaces this chain.

The first
(`Sofic/OsinWeightedMetric.WeightedGreendlingerLeaf`) is refuted by
`not_osinTheorem24`; the second (`WeightedGreendlingerLeafRepaired`) adds
osin24's two clauses and is refuted by
`not_weightedGreendlingerLeafRepaired_of_abelian_partner`.  This one adds the
clause both refutations are really about.

## Three refutations, one cause

* **osin24's witness**: `42` copies of the letter `t` over an alphabet
  containing `t^±42`.  The relator is long in letters and short in the group.
* **the abelian-partner design** (osin24 built it explicitly, from the
  head-injectivity vacuity of `GGT/RelHypLetterPieces.lean`): `U = F₂`,
  `H = Multiplicative ℤ`, an `82`-generator alphabet, two `42`-letter relators
  tying `x` and `y` to integers.  It satisfies **both** of osin24's repairs --
  the relators are geodesic and there are no group pieces -- and still kills
  `⁅x,y⁆`.

Both choose the **alphabet after deciding how long the relators are to be**.
That is the defect, and it is a quantifier order, not a missing predicate.
Osin fixes the relatively hyperbolic structure `(G, {H_λ}, X)` *first*, derives
`μ` and `c`, then for given `λ` and `ε` produces `ρ`, and only then asks for a
symmetrized family of relators **longer than `ρ`**.  The weighted lane replaced
`ρ` by the hard-coded constant `42`, which severs the dependence and lets a
witness enlarge the alphabet until `42` is short.

So `OsinTheorem24Final` below reads

    ∀ G _ L lam, ∃ rho, ∀ R, …

with `rho` chosen after the length function and before the relator family.  No
new predicate is needed; the two clauses osin24 added are kept, because they are
independently necessary.

## Why this excludes both witnesses, and why non-elementarity is the mechanism

*osin24's witness*: at a fixed alphabet the constant word of length `N ≥ ρ` is
not geodesic once `N` exceeds the largest power of `t` in the alphabet, so it is
excluded twice over.

*The abelian design*: with the alphabet fixed, distinct partner letters are a
finite supply, so relators with pairwise distinct letters have bounded length.
Exceeding `ρ` forces a letter to repeat, which creates a group piece and breaks
the metric condition.  An elementary partner factor simply **cannot** supply
arbitrarily long small-cancellation families over a fixed alphabet.

A non-elementary partner can, and that is exactly the mechanism: a free pair
inside `H` gives infinitely many general-position words over one finite
generating set.  So the team lead's instinct to add `IsNonElementaryHyperbolic H`
is right about *where the content is* and belongs on the **design** side, which
already carries it -- `OsinRelatorDesignFinal` demands one length function and
then a design for **every** `ρ`, and that demand is satisfiable precisely when
the partner is non-elementary.  Putting it in the leaf instead would be stating
a hypothesis the leaf's own quantifiers cannot use: the leaf sees an abstract
`RelativeLength`, not a group with a geometry.

osin24 proposed a different third clause, Osin's isolated-components condition
(no two distinct members of `R`, rotations included, traversing a common
peripheral coset along a shared subpath), which `Sofic/OsinWeightedMetric.lean`'s
own `LetterFragmentSlack` paragraph already names as the honest alternative to
porting Osin's component machinery.  That condition is real and may well be
needed too, but it does not explain the two witnesses -- both have a *single*
peripheral letter per relator, so their component-pieces are one letter long,
comfortably inside any `μ·|R|` bound.  What both witnesses exploit is the fixed
`42`.  If a fourth generation turns out to need components as well, it is
additive and this module is where it goes.

## What is proved

The universal closure, the design composition and the endpoint, re-proved over
the final forms; and the model test the standing rule asks for --
`weightedGreendlingerLeafFinal_empty` and `weightedTorsionLeafFinal_empty`
instantiate both leaves at the empty relator family, so the added clauses have
not made them unsatisfiable.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open OsinWeightedMetric

/-! ## 1.  The final leaves -/

/-- **The Greendlinger leaf, final form.**  Geodesic relators and group pieces,
as in the repaired form, plus a length floor `rho` which
`OsinTheorem24Final` chooses *after* the length function and *before* the
relator family. -/
def WeightedGreendlingerLeafFinal {G : Bool → Type} [∀ b, Group (G b)]
    (L : RelativeLength G) (R : Set (List (CoprodI G))) (rho : ℕ) (lam : ℚ) :
    Prop :=
  HasGeodesicSpellings L →
    LetterSymmetrized R → (∀ r ∈ R, LetterReduced L r) →
      (∀ r ∈ R, ∀ a ∈ r, L.len a ≤ 1) →
        (∀ r ∈ R, LetterGeodesic L r) →
          (∀ r ∈ R, rho ≤ r.length) →
            LetterFragmentSlack R lam →
              LetterMetricGroupSmallCancellation R lam →
                RelativeLengthBound L R

/-- **The torsion leaf, final form.** -/
def WeightedTorsionLeafFinal {G : Bool → Type} [∀ b, Group (G b)]
    (L : RelativeLength G) (R : Set (List (CoprodI G))) (rho : ℕ) (lam : ℚ) :
    Prop :=
  HasGeodesicSpellings L →
    LetterSymmetrized R → (∀ r ∈ R, LetterReduced L r) →
      (∀ r ∈ R, ∀ a ∈ r, L.len a ≤ 1) →
        (∀ r ∈ R, LetterGeodesic L r) →
          (∀ r ∈ R, rho ≤ r.length) →
            LetterFragmentSlack R lam →
              LetterMetricGroupSmallCancellation R lam →
                LetterNoProperPower R →
                  TorsionLifts (letterRelatorSubgroup R)

/-- **Osin, Theorem 2.4(1) and 2.4(5), final form.**

The binder order is the theorem's: the geometry `L` and the constant `lam` come
first, `rho` is produced from them, and only then is the relator family
quantified.  Compare `OsinTheorem24` and `OsinTheorem24Repaired`, both refuted,
in which the length floor is the fixed `42` buried inside
`WeightedRouterDesign` and the family may be chosen against it. -/
def OsinTheorem24Final : Prop :=
  ∀ (G : Bool → Type) (_ : ∀ b, Group (G b)) (L : RelativeLength G) (lam : ℚ),
    ∃ rho : ℕ, ∀ R : Set (List (CoprodI G)),
      WeightedGreendlingerLeafFinal L R rho lam ∧
        WeightedTorsionLeafFinal L R rho lam

/-! ## 2.  The model test -/

/-- **The empty family satisfies the final Greendlinger leaf.**  The added
clauses have not made the leaf unsatisfiable; this is the smallest object the
standing model-test rule asks for. -/
theorem weightedGreendlingerLeafFinal_empty {G : Bool → Type} [∀ b, Group (G b)]
    {L : RelativeLength G} {rho : ℕ} {lam : ℚ} :
    WeightedGreendlingerLeafFinal L (∅ : Set (List (CoprodI G))) rho lam :=
  fun _ _ _ _ _ _ _ _ =>
    relativeLengthBound_of_eq_bot letterRelatorSubgroup_empty

/-- **The empty family satisfies the final torsion leaf.** -/
theorem weightedTorsionLeafFinal_empty {G : Bool → Type} [∀ b, Group (G b)]
    {L : RelativeLength G} {rho : ℕ} {lam : ℚ} :
    WeightedTorsionLeafFinal L (∅ : Set (List (CoprodI G))) rho lam :=
  fun _ _ _ _ _ _ _ _ _ => torsionLifts_of_eq_bot letterRelatorSubgroup_empty

/-! ## 3.  The final design -/

/-- **Fournier-Facio's Proposition 2.3, final form.**

One length function, and then a design for **every** length demand `rho`.  That
order is what the final leaf's `∃ rho` forces, and it is the clause an
elementary partner factor cannot meet: with the alphabet fixed, distinct partner
letters are a finite supply, so arbitrarily long relators must repeat a letter
and acquire a group piece.  A non-elementary `H` meets it, because a free pair
inside `H` supplies infinitely many general-position words over one finite
generating set.

`IsNonElementaryHyperbolic H` is therefore not decoration here: it is what makes
the `∀ rho` satisfiable. -/
def OsinRelatorDesignFinal : Prop :=
  ∀ (U H : Type) (_ : Group U) (_ : Group H),
    Group.IsFinitelyPresented U → IsPowerTorsionFree U →
      Infinite H → Group.IsFinitelyPresented H → IsPowerTorsionFree H →
        IsNonElementaryHyperbolic H →
          IsRelativelyHyperbolic (CoprodI (pairFamily U H))
              (fun _ : Unit => freeProductPeripheral U H) →
            ∃ L : RelativeLength (pairFamily U H), ∀ rho : ℕ,
              ∃ D : WeightedRouterDesign U H (pairFamily U H),
                D.relLength = L ∧
                  (∀ r ∈ D.relators, rho ≤ r.length) ∧
                  (∀ r ∈ D.relators, LetterGeodesic D.relLength r) ∧
                  LetterMetricGroupSmallCancellation D.relators (1 / 7)

/-! ## 4.  The composition and the endpoint -/

/-- **The small-cancellation quotient, over the final conditions.** -/
theorem exists_smallCancellationQuotient_final
    (hOsin : OsinTheorem24Final) (hDesign : OsinRelatorDesignFinal)
    (hRelHyp : FreeProductRelativelyHyperbolicStatement)
    (U H : Type) [Group U] [Group H]
    (hUfp : Group.IsFinitelyPresented U) (hUtf : IsPowerTorsionFree U)
    (hHinf : Infinite H) (hHfp : Group.IsFinitelyPresented H)
    (hHtf : IsPowerTorsionFree H) (hHne : IsNonElementaryHyperbolic H) :
    ∃ (P : Type) (_ : Group P),
      Group.IsFinitelyPresented P ∧ IsPowerTorsionFree P ∧
        (∃ p : H →* P, Function.Surjective p) ∧
        (∃ e : U →* P, Function.Injective e) := by
  haveI := hUfp
  haveI := hHfp
  have hrh : IsRelativelyHyperbolic (CoprodI (pairFamily U H))
      (fun _ : Unit => freeProductPeripheral U H) :=
    hRelHyp U H inferInstance inferInstance hHne.1
  obtain ⟨L, hfam⟩ :=
    hDesign U H inferInstance inferInstance hUfp hUtf hHinf hHfp hHtf hHne hrh
  obtain ⟨rho, hleaf⟩ := hOsin (pairFamily U H) inferInstance L (1 / 7)
  obtain ⟨D, hLeq, hlong, hgeo, hgp⟩ := hfam rho
  obtain ⟨hleafG, hleafT⟩ := hleaf D.relators
  rw [← hLeq] at hleafG hleafT
  have hfloor : ∀ r ∈ D.relators, 2 ≤ r.length := by
    intro r hr
    have h := D.relators_long r hr
    omega
  have hbound : RelativeLengthBound D.relLength D.relators :=
    hleafG D.geodesic D.relators_symmetrized D.relators_cyclicallyReduced
      D.relators_letters hgeo hlong D.fragmentSlack hgp
  have hemb : Function.Injective D.emb :=
    (factorMap_source_injective hbound hfloor).comp D.sourceEquiv.injective
  have htors : IsPowerTorsionFree D.Routed :=
    isPowerTorsionFree_of_torsionLifts (D.ambient_torsionFree hUtf hHtf)
      (hleafT D.geodesic D.relators_symmetrized D.relators_cyclicallyReduced
        D.relators_letters hgeo hlong D.fragmentSlack hgp D.relators_noProperPower)
  exact ⟨D.Routed, inferInstance, D.finitelyPresented, htors,
    ⟨D.partnerHom, D.partnerHom_surjective⟩, ⟨D.emb, hemb⟩⟩

/-- **`FournierFacioQuotientStatement` from the final inputs.**  Three named
`Prop`s, as in every generation; what has changed is that the middle one now
demands a design at every length over one fixed geometry, and the first has
Osin's own quantifier order. -/
theorem fournierFacioQuotientStatement_of_osin_final
    (hOsin : OsinTheorem24Final) (hDesign : OsinRelatorDesignFinal)
    (hRelHyp : FreeProductRelativelyHyperbolicStatement) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement := by
  intro H₀ U instH₀ instU hinf hfp htf hhyp hT hUfp hUtf
  exact exists_smallCancellationQuotient_final hOsin hDesign hRelHyp U H₀
    hUfp hUtf hinf hfp htf (isNonElementaryHyperbolic_of_kazhdan' hhyp hT)

end RelHyp
end GGT
end GroupApproximation
