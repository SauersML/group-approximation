import GroupApproximation.GGT.RelHypDefinition
import GroupApproximation.Sofic.OsinWeightedMetric

/-!
# Osin's Theorem 2.4, and the small-cancellation quotient of Fournier-Facio's
Proposition 2.3

D. Osin, *Small cancellations over relatively hyperbolic groups and embedding
theorems*, Ann. of Math. 172 (2010) 1--39, Theorem 2.4; and
Fournier-Facio et al., Proposition 2.3, which applies it to the relatively
hyperbolic pair `(U ∗ H, U)`.

## Which metric, and why it is not the syllable metric

Osin's small cancellation is measured in the alphabet `X ⊔ ℋ`: a **peripheral**
element is one letter, however long it is, and a non-peripheral element costs
its `X`-word length.  Fournier-Facio's relators are `u_k · w_k⁻¹`, one
peripheral letter followed by a long word in `H`, and their length is the
length of `w_k`.

Measuring instead in `Monoid.CoprodI` **syllables** — which is what
`OsinSmallCancellation.wlen` does — collapses `w_k` to a single syllable, so
`u_k · w_k⁻¹` has length two whatever `w_k` is.  That is not a technicality:
the length floor and the fragment slack of the syllable lane both fail at
length two, and the failure is a theorem of this repository rather than a
suspicion.  `RelativeRouterEnvelope.not_partnerSurjective` and
`OsinWeightedMetric.not_relativeLengthBound_of_light_tie` prove that at the
syllable metric a relator identifying a source element with a partner element
**refutes** the length bound: the `ℤ ∗ ℤ/3` witness recorded in
`Sofic/GreendlingerRelativeTransfer` is exactly a relator of this shape.  So a
design stated over `OsinSmallCancellation.wlen` with a length floor and a tie
is not merely unproved -- it is unsatisfiable, and the repository refutes it.

`Sofic/OsinWeightedMetric.lean` is the lane built for this, and it is the one
used here.  Its `RelativeLength` carries exactly Osin's asymmetry as its fifth
clause,

    len_source_le_one : ∀ x : G false, len (CoprodI.of x) ≤ 1

-- every element of the peripheral factor is a single letter, and nothing is
assumed about the other factor -- and its relators are letter lists whose floor
`42 ≤ r.length` counts letters, which a tie relator meets as soon as its
partner element is long.

## What Osin's Theorem 2.4 says, and where its clauses already live

Let `G` be hyperbolic relative to `{H_λ}` with finite relative generating set
`X`.  Osin produces, for suitable parameters, a `ρ` such that every symmetrized
relator family satisfying `C(ε, μ, λ, c, ρ)` has, in `G/⟪R⟫`: (1) each `H_λ`
still injects; (2) the quotient is again relatively hyperbolic; (3)--(4)
structure of `⟪R⟫`; (5) every finite-order element is the image of one of the
same order.  Clauses (1) and (5) are what the Fournier-Facio paragraph
consumes, and `Sofic/OsinWeightedMetric.lean` has already cut them down to two
named predicates on the relator family, `WeightedGreendlingerLeaf` and
`WeightedTorsionLeaf`, both with proved instances.

So Theorem 2.4 is **not** restated here as a fresh monolithic citation.
`OsinTheorem24` is the universal closure of those two leaves, which is faithful
(each leaf carries Osin's own design hypotheses in its binders: geodesic
spellings, symmetrization, cyclic reducedness, letters, fragment slack, the
metric condition, and for the torsion leaf no relator a proper power), is
checkable against definitions rather than against a docstring, and spends the
repository's proved content instead of duplicating it.

## What Proposition 2.3 adds, and why it is a second input

Osin's theorem is about families that satisfy the small-cancellation condition;
it does not say a *useful* one exists.  Fournier-Facio's Proposition 2.3
supplies it: over `G = U ∗ H` with peripheral `U`, one relator `u_k w_k` per
generator of `U`, with `w_k` a long word in `H` in general position -- which is
what Osin's §4 provides in a non-elementary relatively hyperbolic group, and is
the only place hyperbolicity of `H` is really used.  In the quotient each `u_k`
becomes `w_k⁻¹`, so the image of `H` is everything.

`OsinWeightedMetric.WeightedRouterDesign` is precisely that package -- relator
family, its six design certificates, and the **tie** field saying each source
generator is identified with a partner element -- so `OsinRelatorDesign` asks
for one, at the canonical two-factor model `pairFamily U H`.

## What is proved here

`exists_smallCancellationQuotient`: the four clauses
`FournierFacioQuotientStatement` asks for, read off the design.  Three of them
are already leaf-free theorems of `Sofic/OsinWeightedMetric.lean` --
`finitelyPresented`, `partnerHom_surjective` (the surjection `H ↠ P`, which the
tie buys with no diagram argument at all), and the ambient torsion-freeness --
and the remaining two, `emb_injective` and `torsionFree`, spend one leaf each.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open OsinWeightedMetric

/-! ## 1.  Osin's Theorem 2.4, clauses (1) and (5) -/

/-- **Osin, Theorem 2.4(1) and 2.4(5)**, in the two-factor model at the
weighted relative metric: for every relative length function, every relator
family and every constant, the relative Greendlinger lemma and the relative
torsion classification hold.

Each conjunct is the corresponding leaf of `Sofic/OsinWeightedMetric.lean`,
which carries Osin's design hypotheses in its own binders, so this `Prop` is
the honest universal closure of the two open leaves and not a weakening of
them. -/
def OsinTheorem24 : Prop :=
  ∀ (G : Bool → Type) (_ : ∀ b, Group (G b)) (L : RelativeLength G)
    (R : Set (List (CoprodI G))) (lam : ℚ),
      WeightedGreendlingerLeaf L R lam ∧ WeightedTorsionLeaf L R lam

/-! ## 2.  The relator design of Proposition 2.3 -/

/-- **Fournier-Facio, Proposition 2.3**: the choice of relators, and Osin's §4
general position behind it.

Over the relatively hyperbolic pair `(U ∗ H, U)` with `H` non-elementary
hyperbolic, there is a weighted router design: a finite symmetrized family of
letter-reduced relators of at least `42` letters, no one of them a proper
power, satisfying `C'(1/8)`, together with a tie identifying each generator of
the peripheral factor with an element of the other factor.

The ambient family is fixed to be `pairFamily U H`, the canonical model, rather
than an arbitrary `G` with isomorphisms to `U` and `H`; the design's
`sourceEquiv` and `partnerEquiv` are then the identity, and the relative
hyperbolicity hypothesis is about the same group the design is built over.

Non-elementarity and relative hyperbolicity are hypotheses, so the geometric
input is visible in the type.  Osin's §4 is the only step that uses them, and
it uses them to choose the `w_k` in general position: what makes the pieces
short is that distinct long words in a non-elementary hyperbolic group can be
chosen with small overlap, which is false in an elementary one -- in `ℤ` any
two long words share almost all of their length.

## Which non-elementarity, and why it is a hypothesis on `H` and not on the pair

Two different conditions travel under the name.  Osin's Theorem 2.4 itself
needs neither: it is a statement about an arbitrary relatively hyperbolic pair
and an arbitrary family satisfying the small-cancellation condition.  What
needs a non-elementarity hypothesis is the *existence* of a good family, §4,
and there are two candidates for it.

* **Non-elementarity of the pair** -- the action of `U ∗ H` on the coned-off
  graph has two independent loxodromics, `HullGeometry.ActsNonElementarily` in
  this repository's vocabulary.
* **Non-elementarity of `H` as a group** -- `¬ IsElementaryGroup H`, which is
  what `IsNonElementaryHyperbolic H` carries.

The hypothesis here is the second, and deliberately so: the first is too weak
for this application.  Take `H = ℤ` and `U = F₂`.  The pair `(F₂ ∗ ℤ, F₂)` is
relatively hyperbolic and its coned-off graph is quasi-isometric to a tree on
which `F₂ ∗ ℤ` acts non-elementarily, so the pair passes the first test; but
the `w_k` must be chosen inside `H`, every element of `ℤ` is a power of one
generator, and any two long `w`'s overlap in almost their whole length.  No
`C'(1/8)` family of the required shape exists, and indeed none can:
`GGT/RelHypWithoutKazhdan.lean` proves that `F₂` embeds in no quotient of `ℤ`.
So it is `H` that must be non-elementary, and the pair's non-elementarity is
not a substitute.

Nothing is lost in the other direction, so the hypothesis is not too strong
either: if `H` is non-elementary then so is the pair, since two independent
loxodromics of `H` remain independent and loxodromic in the coned-off graph,
the `H`-vertex space being quasi-isometrically embedded once the `U`-cosets are
crushed.  Adding the pair's non-elementarity as a second hypothesis would
therefore be redundant -- and would be actively harmful here, since it is a
hypothesis this development would then have to discharge before it could use
the input, which would open a gap rather than close one. -/
def OsinRelatorDesign : Prop :=
  ∀ (U H : Type) (_ : Group U) (_ : Group H),
    Group.IsFinitelyPresented U → IsPowerTorsionFree U →
      Infinite H → Group.IsFinitelyPresented H → IsPowerTorsionFree H →
        IsNonElementaryHyperbolic H →
          IsRelativelyHyperbolic (CoprodI (pairFamily U H))
              (fun _ : Unit => freeProductPeripheral U H) →
            Nonempty (WeightedRouterDesign U H (pairFamily U H))

/-! ## 3.  The quotient -/

/-- **The small-cancellation quotient of Fournier-Facio's Proposition 2.3.**

From Osin's Theorem 2.4, the relator design, and the relative hyperbolicity of
the free product: a finitely presented torsion-free group `P` in which `U`
embeds and onto which `H` surjects.

Every hypothesis of `OsinRelatorDesign` is discharged here from the hypotheses
of the theorem, so the only literature debt of the conclusion is the three
named `Prop`s in the binder list.  The surjection `H ↠ P` costs no leaf: it is
the design's tie, and `OsinWeightedMetric.WeightedRouterDesign.partnerHom_surjective`
proves it outright. -/
theorem exists_smallCancellationQuotient
    (hOsin : OsinTheorem24) (hDesign : OsinRelatorDesign)
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
  obtain ⟨D⟩ :=
    hDesign U H inferInstance inferInstance hUfp hUtf hHinf hHfp hHtf hHne hrh
  obtain ⟨hleafG, hleafT⟩ :=
    hOsin (pairFamily U H) inferInstance D.relLength D.relators (1 / 7)
  exact ⟨D.Routed, inferInstance, D.finitelyPresented,
    D.torsionFree hleafT hUtf hHtf,
    ⟨D.partnerHom, D.partnerHom_surjective⟩,
    ⟨D.emb, D.emb_injective hleafG⟩⟩

end RelHyp
end GGT
end GroupApproximation
