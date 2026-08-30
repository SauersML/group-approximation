import GroupApproximation.GGT.RelHypFreeProductElementaryClosure
import GroupApproximation.GGT.RelHypFreeProductPartnerFills

/-!
# The suitability residue, moved off the free product and onto one group

`GGT/RelHypProp23FromOsin24.lean` derives Fournier-Facio's Proposition 2.3 from
Osin's Theorem 2.4 plus one named input, `FreeProductSuitabilityStatement`:
that the image of `H` is a suitable subgroup (Osin, Definition 2.2) of `U ∗ H`
relative to the single peripheral factor `U`.  That input is stated over a free
product, and its docstring attributes the whole of it to Osin's Theorem 2.1 and
Lemma 2.3.

This module shows that the free-product half of it is not a citation at all.
Everything about `U` is discharged here, by a retraction and one lemma of the
union-geometry chain, and what survives is a statement about `H` alone:

> a non-elementary torsion-free hyperbolic group contains two non-commensurable
> elements of infinite order whose maximal elementary subgroups meet trivially.

`HyperbolicSuitabilityStatement` is that sentence, written with the same
`IsSuitableSubgroup` predicate at the empty peripheral family --- "`H` is
suitable in itself" --- and `isSuitableSubgroup_freeProduct_of_partner` is the
reduction.

## The retraction does three of the four clauses

`partnerRetraction : U ∗ H →* H` kills the peripheral factor and is the
identity on the partner.  Applying it to the defining equation:

* a conjugate of `of y` into `U` maps to `1 = ρ(c)⁻¹ y ρ(c)`, so `y = 1` --- the
  witnesses are hyperbolic elements in Osin's sense, with no normal form;
* a commensurability `c⁻¹ (of y₁)^k c = (of y₂)^l` maps to a commensurability of
  `y₁` and `y₂` inside `H`, so non-commensurability transfers by
  contraposition;
* infinite order is `Monoid.CoprodI.of_injective`.

Only the fourth clause needs the free product's normal form, and that lemma
already exists: `exists_factor_of_mem_osinElementaryClosure` puts `E(of y)`
inside the image of `H`, after which `of_injective` turns membership in the
ambient elementary closure into membership in `E_H(y)`.

## The residue is real, and this is what it costs

`HyperbolicSuitabilityStatement` is **not** proved here, and it does not close
at this revision.  Two theorems stand behind it, and neither is in Mathlib nor
in this repository:

* that a non-elementary hyperbolic group contains two independent loxodromic
  elements --- ping-pong on the boundary, or the Tits alternative;
* Osin's Theorem 6.8 for `E_H(x)`.  For the actual trivial-intersection clause,
  the full stronger classification of a torsion-free virtually cyclic group as
  cyclic is unnecessary: torsion-freeness makes a nontrivial common member
  infinite-order, and the finite-index conclusion gives it a common power with
  each witness.  Aligning those two powers contradicts non-commensurability.
  This exact reduction is proved in `GGT/RelHypSuitabilityClosure.lean`; the
  leaf is **not** the Morse lemma.

So the honest report is a shrunken citation, not a discharge: what was "Osin's
Theorem 2.1 and Lemma 2.3, at a free product" is now one sentence about one
hyperbolic group, with the free product gone.

## The two halves are named separately

Those two theorems have different homes, so section 5a splits the residue into
`HyperbolicNonCommensurablePairStatement` --- the pair, usually called two
independent loxodromics but really two loxodromics in distinct commensurability
classes --- and `HyperbolicElementaryClosureStatement` --- the elementary
closures, classically that `E_H(x)` is the maximal cyclic subgroup containing
`x`.  `hyperbolicSuitabilityStatement_of_split` recovers the unsplit
`Prop`, so nothing downstream moves; the reverse derivation recovers half (a)
only, and the docstring of
`hyperbolicNonCommensurablePairStatement_of_suitability` says why the conjunction
is deliberately the stronger statement.

Section 5b records, with a proof, that the obvious geometric route to half (a)
is not merely unpriced but **closed**: conjugation preserves commensurability, so
no condition that a conjugate pair satisfies --- divergence of axes included ---
can imply `¬ OsinCommensurable`.

## The first positive witness

`RelHypOsinTheorem24Verbatim.lean`'s model-test section records that "no
*positive* witness of `IsSuitableSubgroup` exists in this repository today", and
calls the absence structural.  It is not.  Reading the free group of rank two as
`ℤ ∗ ℤ` makes every clause of Definition 2.2 checkable by the two coordinate
retractions and the elementary-closure lemma, and `isSuitableSubgroup_intPair`
proves it.  Composed with the reduction,
`isSuitableSubgroup_freeProduct_intPair` inhabits the predicate at the
Fournier-Facio configuration itself --- a *nonempty* peripheral family, an
arbitrary peripheral factor --- which is the strongest model test available
short of the theorem.

## What the tests do and do not pin

The negative side is `not_isSuitableSubgroup_top_of_comm`: no abelian group is
suitable in itself, so the conclusion of `HyperbolicSuitabilityStatement` is not
satisfied by objects Osin's theorem says nothing about, and in particular not by
the trivial group or by `ℤ`.

One thing is **not** pinned, and is recorded rather than hidden.  Nothing in
this repository exhibits a group satisfying `IsNonElementaryHyperbolic`: the
only route to non-elementarity here is `isNonElementaryHyperbolic_of_kazhdan`,
which consumes the named input `ElementaryAmenableStatement` and a Kazhdan
group.  So a future proof of `HyperbolicSuitabilityStatement` must not be an
argument from vacuity of its hypothesis.  This is not a debt introduced here ---
`FournierFacioProposition23` already quantifies over the same class --- but it
is the failure mode this particular `Prop` invites, so it is written down.

## An elaboration trap, met twice

The index of `CoprodI.of` must be pinned on the *function*, never by ascribing
the argument.  A type ascription elaborates its term at the ascribed type but
reports the term's own inferred type, so `(y : pairFamily U H true)` hands the
elaborator a `y : H` and leaves the index an unassigned metavariable.  Every
statement below therefore goes through `freeProductPartnerHom` or through an
ascription on `CoprodI.of` itself.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid

/-! ## 0.  One group-theoretic triviality -/

/-- Conjugation reflects triviality, in the `c⁻¹ x c` orientation. -/
theorem eq_one_of_inv_conj_eq_one {K : Type*} [Group K] {c x : K}
    (h : c⁻¹ * x * c = 1) : x = 1 := by
  have h2 : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
  rw [h, mul_one, mul_inv_cancel] at h2
  exact h2

/-! ## 1.  The retraction of `U ∗ H` onto the partner factor -/

section Retraction

variable {U H : Type} [Group U] [Group H]

/-- The factorwise data of the retraction onto the partner factor: the trivial
map on the peripheral factor, the identity on the partner. -/
def partnerRetractionFactor (U H : Type) [Group U] [Group H] :
    ∀ b, pairFamily U H b →* H
  | false => (1 : U →* H)
  | true => MonoidHom.id H

/-- **The retraction `U ∗ H →* H`.**  It exists because a free product has the
universal property, and it is what makes three of the four clauses of Osin's
Definition 2.2 free of word combinatorics. -/
def partnerRetraction (U H : Type) [Group U] [Group H] :
    CoprodI (pairFamily U H) →* H :=
  CoprodI.lift (partnerRetractionFactor U H)

@[simp] theorem partnerRetraction_of_partner (y : pairFamily U H true) :
    partnerRetraction U H (CoprodI.of y) = y :=
  CoprodI.lift_of (partnerRetractionFactor U H) y

@[simp] theorem partnerRetraction_of_source (x : pairFamily U H false) :
    partnerRetraction U H (CoprodI.of x) = 1 :=
  CoprodI.lift_of (partnerRetractionFactor U H) x

@[simp] theorem partnerRetraction_partnerHom (y : H) :
    partnerRetraction U H (freeProductPartnerHom U H y) = y := by
  rw [freeProductPartnerHom_apply]
  exact partnerRetraction_of_partner y

end Retraction

/-! ## 2.  The three transfers -/

section Transfer

variable {U H : Type} [Group U] [Group H]

/-- **A nontrivial partner element is hyperbolic in Osin's sense.**  Were it
conjugate into the peripheral factor, the retraction would read that conjugacy
as `1 = ρ(c)⁻¹ y ρ(c)`. -/
theorem isHyperbolicElement_of_partner {y : H} (hy : y ≠ 1) :
    IsHyperbolicElement (fun _ : Unit => freeProductPeripheral U H)
      (freeProductPartnerHom U H y) := by
  intro hpar
  obtain ⟨_l, c, hc⟩ := hpar
  simp only [freeProductPeripheral, MonoidHom.mem_range] at hc
  obtain ⟨u, hu⟩ := hc
  refine hy ?_
  have h := congrArg (partnerRetraction U H) hu
  simp only [map_mul, map_inv, partnerRetraction_of_source,
    partnerRetraction_partnerHom] at h
  exact eq_one_of_inv_conj_eq_one h.symm

/-- **A partner element of infinite order stays of infinite order.**  Purely
`Monoid.CoprodI.of_injective`. -/
theorem pow_ne_one_of_partner {y : H} (hy : ∀ n : ℕ, 0 < n → y ^ n ≠ 1)
    (n : ℕ) (hn : 0 < n) : (freeProductPartnerHom U H y) ^ n ≠ 1 := by
  intro hcon
  rw [← map_pow] at hcon
  refine hy n hn ?_
  have h := congrArg (partnerRetraction U H) hcon
  simpa using h

/-- **Commensurability in the free product is commensurability in the factor.**
The retraction carries the conjugator. -/
theorem osinCommensurable_of_partner {y₁ y₂ : H}
    (h : OsinCommensurable (freeProductPartnerHom U H y₁)
      (freeProductPartnerHom U H y₂)) : OsinCommensurable y₁ y₂ := by
  obtain ⟨k, l, c, hk, hl, hc⟩ := h
  refine ⟨k, l, partnerRetraction U H c, hk, hl, ?_⟩
  have h := congrArg (partnerRetraction U H) hc
  simpa only [map_mul, map_inv, map_zpow, partnerRetraction_partnerHom] using h

end Transfer

/-! ## 3.  Membership in the elementary closure descends to the factor -/

/-- **A factor element in the elementary closure of a factor element is in the
factor's elementary closure.**  One application of `CoprodI.of_injective` in
each of the two branches of Osin's `±n`. -/
theorem mem_osinElementaryClosure_of_of {ι : Type} {G : ι → Type}
    [∀ i, Group (G i)] {i : ι} {x z : G i}
    (h : (CoprodI.of z : CoprodI G) ∈
      osinElementaryClosure (CoprodI.of x : CoprodI G)) :
    z ∈ osinElementaryClosure x := by
  obtain ⟨n, hn, hcase⟩ := h
  refine ⟨n, hn, ?_⟩
  rcases hcase with hc | hc
  · refine Or.inl (CoprodI.of_injective i ?_)
    simpa using hc
  · refine Or.inr (CoprodI.of_injective i ?_)
    simpa using hc

/-! ## 4.  The reduction -/

/-- **Suitability of the partner factor in `U ∗ H` from suitability of `H` in
itself.**

The peripheral family is the single factor `U` and the subgroup is the image of
`H`, which is exactly the configuration `FreeProductSuitabilityStatement` names.
Nothing about `U` is assumed: the free product contributes only the fourth
clause, and there the union-geometry lemma already puts every element of the
ambient elementary closure inside the image of `H`. -/
theorem isSuitableSubgroup_freeProduct_of_partner (U H : Type) [Group U] [Group H]
    (h : IsSuitableSubgroup (fun _ : Empty => (⊥ : Subgroup H)) (⊤ : Subgroup H)) :
    IsSuitableSubgroup (fun _ : Unit => freeProductPeripheral U H)
      (MonoidHom.range (freeProductPartnerHom U H)) := by
  obtain ⟨y₁, -, y₂, -, -, -, hord₁, hord₂, hncom, htriv⟩ := h
  have hy₁ : y₁ ≠ 1 := fun hcon => hord₁ 1 one_pos (by rw [hcon, one_pow])
  have hy₂ : y₂ ≠ 1 := fun hcon => hord₂ 1 one_pos (by rw [hcon, one_pow])
  refine ⟨freeProductPartnerHom U H y₁, ⟨y₁, rfl⟩,
    freeProductPartnerHom U H y₂, ⟨y₂, rfl⟩,
    isHyperbolicElement_of_partner hy₁, isHyperbolicElement_of_partner hy₂,
    pow_ne_one_of_partner hord₁, pow_ne_one_of_partner hord₂,
    fun hcon => hncom (osinCommensurable_of_partner hcon), ?_⟩
  intro f hf₁ hf₂
  rw [freeProductPartnerHom_apply] at hf₁ hf₂
  obtain ⟨z, hz⟩ :=
    exists_factor_of_mem_osinElementaryClosure (G := pairFamily U H) (i := true)
      (x := y₁) hord₁ hf₁
  have hz₁ : z ∈ osinElementaryClosure y₁ :=
    mem_osinElementaryClosure_of_of (by rw [hz]; exact hf₁)
  have hz₂ : z ∈ osinElementaryClosure y₂ :=
    mem_osinElementaryClosure_of_of (by rw [hz]; exact hf₂)
  have hz1 : z = (1 : pairFamily U H true) := htriv z hz₁ hz₂
  rw [← hz, hz1]
  exact map_one _

/-! ## 5.  The residue, named -/

/-- **The suitability residue, at one group and no free product.**

Osin's Definition 2.2 read with an empty peripheral family --- every element is
then hyperbolic in his sense, by `isHyperbolicElement_of_isEmpty` --- so this
says exactly: `H` contains two non-commensurable elements of infinite order
whose maximal elementary subgroups meet trivially.

This is what is left of `FreeProductSuitabilityStatement` after
`isSuitableSubgroup_freeProduct_of_partner`, and it is Osin's Theorem 2.1
together with his Lemma 2.3.  It is not proved here; the header says what the
two missing theorems are. -/
def HyperbolicSuitabilityStatement : Prop :=
  ∀ (H : Type) (_ : Group H),
    IsNonElementaryHyperbolic H → IsPowerTorsionFree H →
      IsSuitableSubgroup (fun _ : Empty => (⊥ : Subgroup H)) (⊤ : Subgroup H)

/-- **The residue implies the free-product statement**, at every peripheral
factor at once.  Stated in the body form of
`GGT/RelHypProp23FromOsin24.FreeProductSuitabilityStatement`, so that it
discharges that field without this module importing it. -/
theorem isSuitableSubgroup_freeProduct_of_hyperbolicSuitability
    (h : HyperbolicSuitabilityStatement) (U H : Type) [Group U] [Group H]
    (hne : IsNonElementaryHyperbolic H) (htf : IsPowerTorsionFree H) :
    IsSuitableSubgroup (fun _ : Unit => freeProductPeripheral U H)
      (MonoidHom.range (freeProductPartnerHom U H)) :=
  isSuitableSubgroup_freeProduct_of_partner U H (h H inferInstance hne htf)

/-! ## 5a.  The residue, split into its two halves

The two halves have different homes and will be discharged by different
machinery, so they are named separately.  `HyperbolicSuitabilityStatement` is
kept exactly as it was, and `hyperbolicSuitabilityStatement_of_split` derives
it, so every consumer downstream of it is untouched. -/

/-- **Half (a): a non-commensurable pair of infinite-order elements.**

Usually called "two independent loxodromics", and that name is misleading here:
independence in the geometric sense is strictly weaker than what this asks.  The
honest reading is **two loxodromics in distinct commensurability classes**, and
the gap between the two readings is exactly the conjugate case --- see section 5b.

The nearest classical leaf is Gromov's and Delzant's theorem that a
non-elementary hyperbolic group contains a free subgroup of rank two.  **That
does not close this either**, and the reason is worth stating because it is the
third appearance of one mis-costing (the free-pair route to `E(a) = ⟨a⟩` died of
it, and so did the geometric route in section 5b): free generators are
non-commensurable *inside the free subgroup*, but `OsinCommensurable` quantifies
the conjugator over **all of `H`**, and freeness constrains nothing about
conjugators lying outside the subgroup.  Two generators of a free subgroup can
still be conjugate in the ambient group, and conjugate elements are
commensurable (`osinCommensurable_conj`).

So the obligation that actually remains is ruling out conjugacy, which is an
`E(g)` question rather than a ping-pong one; half (a) is homed with the
elementary-closure layer, and it is where Osin's Lemma 2.3 sits.

**The order is load-bearing: prove half (b) first.**  The two halves are named
separately because they have different leaves, not because either can be
attacked in isolation, and nothing here licenses starting with (a).  Every
known route to (a) dies at the conjugate case (section 5b), and the one
statement that eliminates the offending quantifier over conjugators --- Coulon's
`pseudo nu = 1`, section 5c --- is available only once (b) has supplied
"`E(x)` is the maximal cyclic subgroup containing `x`".  Reading the split as
two independent halves and beginning with (a) is therefore not a slower path
but a path with no proof at the end of it.

dgo-611-lane's isolated-component machinery was examined for this and does not
reach it: it needs a coned-off graph and unboundedness of `d̂_λ`, which
`IsNonElementaryHyperbolic` does not supply, and even granted that input it
produces one loxodromic rather than a pair. -/
def HyperbolicNonCommensurablePairStatement : Prop :=
  ∀ (H : Type) (_ : Group H),
    IsNonElementaryHyperbolic H → IsPowerTorsionFree H →
      ∃ f₁ f₂ : H,
        (∀ n : ℕ, 0 < n → f₁ ^ n ≠ 1) ∧ (∀ n : ℕ, 0 < n → f₂ ^ n ≠ 1) ∧
          ¬ OsinCommensurable f₁ f₂

/-- **Half (b): non-commensurable elements have trivially meeting elementary
closures.**

This follows from the usual stronger description "`E_H(x)` is the maximal
cyclic subgroup containing `x`", but does not require proving that description.
The exact argument needs only that every infinite cyclic subgroup of `E_H(x)`
meets `⟨x⟩` nontrivially.  It is a fact about the group's own Cayley graph and
belongs with the hyperbolic-group geometry, not with the relative machinery.

**Its residue is smaller than the geometric framing suggests, and does not
include the Morse lemma.**  DGO reach `E(x)` control through Lemma 4.21(b),
proved from Proposition 4.14's isolated-component counting, because *their*
action is on a coned-off graph and is not acylindrical.  The action here is not
that one: `H` is hyperbolic with a **finite** generating set acting on its own
Cayley graph, and this tree already proves such an action acylindrical
(`GGT.isAcylindrical_cayley_of_finite`) and derives WPD from acylindricity
(`GGT.isWPDAt_of_isAcylindrical`), both unconditionally.  So the
WPD/acylindricity layer is free here.

What is actually owed is **Osin's Theorem 6.8** ---
`GGT.ElementaryOsinSNormal.ElementaryClosureVirtuallyCyclic`, `E(g)` virtually
cyclic for a loxodromic of an acylindrical action, which occurs in this tree only
as a hypothesis and is never concluded, so it is a genuine leaf.  The necessary
torsion-free upgrade is now proved in `GGT/RelHypSuitabilityClosure.lean`: it is
the elementwise common-power argument, strictly weaker than classifying the
whole virtually cyclic group as cyclic.  Reports that this
dependence has been eliminated refer to the Lemma 7.1 / `ActsNonElementarily`
chain in `GGT/ElementaryCentralizerAxis.lean` and `GGT/ElementaryBowditch.lean`;
that elimination is real but local to a chain whose conclusion is geometric
independence, which section 5b shows is strictly weaker than what half (a) needs,
and the `Prop` remains a live hypothesis at `GGT/ElementaryProperClosure.lean`
and `GGT/HullYiLoxRadical.lean`.

Stated universally, over every non-commensurable pair, because that is the form
in which it is true and will be proved.  See
`hyperbolicSuitabilityStatement_of_split` for the consequence of that choice. -/
def HyperbolicElementaryClosureStatement : Prop :=
  ∀ (H : Type) (_ : Group H),
    IsNonElementaryHyperbolic H → IsPowerTorsionFree H →
      ∀ f₁ f₂ : H,
        (∀ n : ℕ, 0 < n → f₁ ^ n ≠ 1) → (∀ n : ℕ, 0 < n → f₂ ^ n ≠ 1) →
          ¬ OsinCommensurable f₁ f₂ →
            ∀ f, f ∈ osinElementaryClosure f₁ → f ∈ osinElementaryClosure f₂ →
              f = 1

/-- **The two halves give the residue.**  So a consumer of
`HyperbolicSuitabilityStatement` --- and hence of
`FreeProductSuitabilityStatement`, and hence the Fournier-Facio bridge --- never
has to move when the halves are discharged separately. -/
theorem hyperbolicSuitabilityStatement_of_split
    (ha : HyperbolicNonCommensurablePairStatement)
    (hb : HyperbolicElementaryClosureStatement) :
    HyperbolicSuitabilityStatement := by
  intro H instH hne htf
  obtain ⟨f₁, f₂, ho₁, ho₂, hnc⟩ := ha H instH hne htf
  exact ⟨f₁, Subgroup.mem_top _, f₂, Subgroup.mem_top _,
    isHyperbolicElement_of_isEmpty _ _, isHyperbolicElement_of_isEmpty _ _,
    ho₁, ho₂, hnc, hb H instH hne htf f₁ f₂ ho₁ ho₂ hnc⟩

/-- **The residue gives half (a).**  The other direction of the split, as far as
it goes.

It does **not** give half (b), and that asymmetry is deliberate rather than an
omission: the residue produces *one* pair with trivially meeting elementary
closures, while (b) is a statement about *every* non-commensurable pair.  So the
conjunction is strictly stronger than `HyperbolicSuitabilityStatement`.  Weakening
(b) to restore an equivalence would scope it to an unnamed pair and destroy the
statement a prover would actually attack, so the strength is kept and the gap is
recorded here. -/
theorem hyperbolicNonCommensurablePairStatement_of_suitability
    (h : HyperbolicSuitabilityStatement) :
    HyperbolicNonCommensurablePairStatement := by
  intro H instH hne htf
  obtain ⟨f₁, -, f₂, -, -, -, ho₁, ho₂, hnc, -⟩ := h H instH hne htf
  exact ⟨f₁, f₂, ho₁, ho₂, hnc⟩

/-! ## 5b.  Why the geometric route to half (a) does not close it

`HullGeometry.ActsNonElementarily S x` is *defined* as two loxodromic elements of
`S` that are `HullGeometry.Independent` at `x`, so it is tempting to read any
producer of it as discharging half (a) outright, with the step from geometric
independence to `¬ OsinCommensurable` as a cheap bridge.

**That bridge does not exist: the implication is false.**  `Independent g h x` is
`∃ C, ∀ n m : ℤ, gromovProduct ((gⁿ) • x) ((hᵐ) • x) x ≤ C`, a statement that the
two power orbits diverge.  A conjugate pair diverges in exactly that sense while
being commensurable on the nose.  In the free group of rank two acting on its own
Cayley graph, `f₁ = a` and `f₂ = b⁻¹ a b` have power orbits `aⁿ` and `b⁻¹ aᵐ b`
whose geodesics from `1` share no first letter, so their Gromov products are
bounded and `Independent a (b⁻¹ a b) 1` holds --- and yet
`OsinCommensurable a (b⁻¹ a b)` holds too, with `k = l = 1` and conjugator `b`.

The algebraic half of that witness is proved below and is what makes the point
without any metric machinery: **conjugation preserves commensurability**, so no
predicate that a conjugate pair can satisfy will ever imply
`¬ OsinCommensurable`.  Geometric divergence of axes is such a predicate.

It is why half (a) is stated with Osin's `OsinCommensurable`, whose conjugator
is what makes it the strong form.

**`GGT.ElementaryOsinSNormal.IndependentOfNoCommonZpow` is not a counterexample
to any of this, and is not on the same reef** --- worth saying, because its
weak-looking hypothesis invites the confusion.  It runs the *other* way,

    ∀ a b, IsLoxodromic a x → IsLoxodromic b x →
      (∀ p q : ℤ, p ≠ 0 → q ≠ 0 → a ^ p ≠ b ^ q) → Independent a b x

i.e. weak algebraic ⟹ geometric.  That is Osin's Lemma 6.5, it is sound, and it
is proved unconditionally in this tree as
`GGT.ElementaryIndependence.independentOfNoCommonZpow_of_geodesic`.  Conjugate
pairs satisfy its hypothesis and are indeed `Independent`, so its conclusion
holds of them; nothing is broken.  What that theorem shows is that the geometric
layer sits *downstream* of the weak algebraic condition, and half (a)'s target
--- the strong, conjugator-quantified condition --- sits above both.  There is
no route up. -/

/-- **Conjugate elements are commensurable**, with `k = l = 1`. -/
theorem osinCommensurable_conj {K : Type*} [Group K] (f c : K) :
    OsinCommensurable f (c⁻¹ * f * c) :=
  ⟨1, 1, c, one_ne_zero, one_ne_zero, by simp⟩

/-- **A non-commensurable pair is not a conjugate pair.**  The contrapositive of
`osinCommensurable_conj`, and the form half (a) is used in: whatever produces the
pair must rule out conjugacy, which no divergence-of-axes condition does. -/
theorem ne_conj_of_not_osinCommensurable {K : Type*} [Group K] {f₁ f₂ : K}
    (h : ¬ OsinCommensurable f₁ f₂) (c : K) : c⁻¹ * f₁ * c ≠ f₂ := by
  intro hcon
  exact h (hcon ▸ osinCommensurable_conj f₁ c)

/-! ## 5c.  The conjugator, and where Coulon's lemma sits

Every route to half (a) has died at the same seam --- conjugation moves an axis
without moving the conjugacy class --- so the lemmas that *see* the conjugator
are the ones worth having outright.  Two are unconditional and are proved here.

**Coulon**, arXiv:1302.6933, `1_hyperbolic_geometry.tex`, "pseudo nu = 1":

> Assume that every elementary subgroup of `G` is cyclic.  Let `g, h ∈ G`.  If
> `g` and `hgh⁻¹` generate an elementary subgroup then so do `g` and `h`.

That is exactly the conjugate-form statement half (a) needs, and it is the first
result found that eliminates the conjugator rather than being defeated by it.
Two things about it are worth recording before anyone budgets for it.

**Its proof is boundary-based, and this repository has no boundary.**  Coulon
argues that `g` and `hgh⁻¹` are hyperbolic isometries with the same accumulation
points in `∂X`, so `h` stabilises `{g⁻, g⁺}` and therefore lies in `E(g)`.
Nothing in this tree carries `∂X`, so a literal transcription is not available.

**But over a torsion-free ambient it has a purely algebraic proof, and that
proof is downstream of half (b).**  If `⟨g, hgh⁻¹⟩` is elementary hence cyclic,
then `E(hgh⁻¹) = h E(g) h⁻¹` --- the equivariance proved below --- and by
uniqueness of the maximal cyclic subgroup containing an element of infinite
order that subgroup is `E(g)` again, so `h` normalises `E(g)`; the inversion
case `h r h⁻¹ = r⁻¹` forces `r²ᵐ = 1` and dies on torsion-freeness, leaving
`h ∈ E(g)`.  No boundary is used --- but "`E(x)` is the maximal cyclic subgroup
containing `x`" is precisely half (b).

So Coulon's lemma is **not an independent input to half (a)**: it is the bridge
that converts half (b) into leverage on half (a), which is the sequencing
`HyperbolicElementaryClosureStatement` was already suspected to have.  Budget it
after (b), not beside it. -/

/-- **The elementary closure is conjugation-equivariant.**  Unconditional, and
the fact every route through the conjugator needs: it is what makes "`E(f₁)` and
`E(f₂)` are conjugate" a well-posed statement. -/
theorem mem_osinElementaryClosure_conj {K : Type*} [Group K] {g f : K} (h : K) :
    f ∈ osinElementaryClosure g →
      h * f * h⁻¹ ∈ osinElementaryClosure (h * g * h⁻¹) := by
  rintro ⟨n, hn, hc | hc⟩
  · refine ⟨n, hn, Or.inl ?_⟩
    rw [conj_pow]
    have hstep : (h * f * h⁻¹)⁻¹ * (h * g ^ n * h⁻¹) * (h * f * h⁻¹)
        = h * (f⁻¹ * g ^ n * f) * h⁻¹ := by group
    rw [hstep, hc]
  · refine ⟨n, hn, Or.inr ?_⟩
    rw [conj_pow]
    have hstep : (h * f * h⁻¹)⁻¹ * (h * g ^ n * h⁻¹) * (h * f * h⁻¹)
        = h * (f⁻¹ * g ^ n * f) * h⁻¹ := by group
    rw [hstep, hc]
    group

/-- **A conjugator that centralises `g` lies in `E(g)`.**  The `n = 1` case of
the definition, recorded because it is the shape the algebraic proof of Coulon's
lemma finishes with. -/
theorem mem_osinElementaryClosure_of_conj_eq_self {K : Type*} [Group K] {g h : K}
    (hc : h⁻¹ * g * h = g) : h ∈ osinElementaryClosure g :=
  ⟨1, one_pos, Or.inl (by rw [pow_one]; exact hc)⟩

/-- **A conjugator that inverts `g` lies in `E(g)` too.**  Osin's `±` is what
makes this a membership rather than a failure; over a torsion-free ambient this
branch is the one that dies, which is where torsion-freeness enters the
algebraic proof of Coulon's lemma. -/
theorem mem_osinElementaryClosure_of_conj_eq_inv {K : Type*} [Group K] {g h : K}
    (hc : h⁻¹ * g * h = g⁻¹) : h ∈ osinElementaryClosure g :=
  ⟨1, one_pos, Or.inr (by rw [pow_one]; exact hc)⟩

/-! ## 6.  The negative model test -/

/-- **No abelian group is suitable in itself.**  So the conclusion of
`HyperbolicSuitabilityStatement` fails at the trivial group and at `ℤ`, which is
the check that the residue is not satisfied by objects Osin's theorem says
nothing about. -/
theorem not_isSuitableSubgroup_top_of_comm {K : Type} [Group K]
    (hK : ∀ x y : K, x * y = y * x) :
    ¬ IsSuitableSubgroup (fun _ : Empty => (⊥ : Subgroup K)) (⊤ : Subgroup K) :=
  not_isSuitableSubgroup_of_comm hK _ _

/-! ## 7.  The positive witness: `ℤ ∗ ℤ` -/

/-- The free group of rank two, read as a free product of two copies of `ℤ`. -/
abbrev intPair : Fin 2 → Type := fun _ => Multiplicative ℤ

/-- The generator of either factor. -/
def intGen : Multiplicative ℤ := Multiplicative.ofAdd (1 : ℤ)

theorem intGen_ne_one : intGen ≠ 1 := by
  intro h
  have h2 := congrArg Multiplicative.toAdd h
  simp [intGen] at h2

theorem intGen_pow_ne_one (n : ℕ) (hn : 0 < n) : intGen ^ n ≠ 1 := by
  intro h
  exact intGen_ne_one (IsPowerTorsionFree.of_isMulTorsionFree intGen n hn h)

theorem intGen_zpow_ne_one {l : ℤ} (hl : l ≠ 0) : intGen ^ l ≠ 1 := by
  intro h
  refine hl ?_
  have h2 := congrArg Multiplicative.toAdd h
  rw [toAdd_zpow] at h2
  simpa [intGen] using h2

/-- The factorwise data of the retraction onto the `i`-th coordinate. -/
def intCoordFactor (i : Fin 2) : ∀ j, intPair j →* Multiplicative ℤ :=
  fun j => if j = i then MonoidHom.id (Multiplicative ℤ) else 1

/-- **The retraction of `ℤ ∗ ℤ` onto its `i`-th factor.** -/
def intRetraction (i : Fin 2) : CoprodI intPair →* Multiplicative ℤ :=
  CoprodI.lift (intCoordFactor i)

theorem intRetraction_same (i : Fin 2) (x : intPair i) :
    intRetraction i (CoprodI.of x) = x := by
  have h := CoprodI.lift_of (intCoordFactor i) x
  rw [intRetraction, h, intCoordFactor]
  simp

theorem intRetraction_other {i j : Fin 2} (hij : j ≠ i) (x : intPair j) :
    intRetraction i (CoprodI.of x) = 1 := by
  have h := CoprodI.lift_of (intCoordFactor i) x
  rw [intRetraction, h, intCoordFactor]
  simp [hij]

theorem not_osinCommensurable_intGen :
    ¬ OsinCommensurable
        (CoprodI.of (M := intPair) (i := 0) intGen)
        (CoprodI.of (M := intPair) (i := 1) intGen) := by
  rintro ⟨k, l, c, -, hl, hc⟩
  have h := congrArg (intRetraction 1) hc
  simp only [map_mul, map_inv, map_zpow] at h
  rw [intRetraction_other (show (0 : Fin 2) ≠ 1 by decide),
    intRetraction_same] at h
  simp only [one_zpow, mul_one, inv_mul_cancel] at h
  exact intGen_zpow_ne_one hl h.symm

/-- **`ℤ ∗ ℤ` is suitable in itself**, in Osin's sense, at the empty peripheral
family: the first positive witness of `IsSuitableSubgroup` in this development.

Both generators have infinite order because `ℤ` does and `CoprodI.of` is
injective; they are non-commensurable because the second coordinate retraction
kills one and not the other; and their elementary closures meet trivially
because `exists_factor_of_mem_osinElementaryClosure` confines each to its own
factor, and the two factors meet in `1`. -/
theorem isSuitableSubgroup_intPair :
    IsSuitableSubgroup (fun _ : Empty => (⊥ : Subgroup (CoprodI intPair)))
      (⊤ : Subgroup (CoprodI intPair)) := by
  refine ⟨CoprodI.of (M := intPair) (i := 0) intGen, Subgroup.mem_top _,
    CoprodI.of (M := intPair) (i := 1) intGen, Subgroup.mem_top _,
    isHyperbolicElement_of_isEmpty _ _, isHyperbolicElement_of_isEmpty _ _,
    ?_, ?_, not_osinCommensurable_intGen, ?_⟩
  · intro n hn hcon
    rw [← map_pow] at hcon
    refine intGen_pow_ne_one n hn ?_
    have h := congrArg (intRetraction 0) hcon
    rw [intRetraction_same] at h
    simpa using h
  · intro n hn hcon
    rw [← map_pow] at hcon
    refine intGen_pow_ne_one n hn ?_
    have h := congrArg (intRetraction 1) hcon
    rw [intRetraction_same] at h
    simpa using h
  · intro f hf₁ hf₂
    obtain ⟨z₀, hz₀⟩ :=
      exists_factor_of_mem_osinElementaryClosure (G := intPair)
        (i := (0 : Fin 2)) (x := intGen) intGen_pow_ne_one hf₁
    obtain ⟨z₁, hz₁⟩ :=
      exists_factor_of_mem_osinElementaryClosure (G := intPair)
        (i := (1 : Fin 2)) (x := intGen) intGen_pow_ne_one hf₂
    have hzz : (CoprodI.of z₀ : CoprodI intPair) = CoprodI.of z₁ := by
      rw [hz₀, hz₁]
    have h0 := congrArg (intRetraction 0) hzz
    rw [intRetraction_same,
      intRetraction_other (show (1 : Fin 2) ≠ 0 by decide)] at h0
    rw [← hz₀, h0, map_one]

/-- **A positive witness at the Fournier-Facio configuration itself**: a
nonempty peripheral family, an arbitrary peripheral factor, and the image of the
partner suitable in the free product. -/
theorem isSuitableSubgroup_freeProduct_intPair (U : Type) [Group U] :
    IsSuitableSubgroup
      (fun _ : Unit => freeProductPeripheral U (CoprodI intPair))
      (MonoidHom.range (freeProductPartnerHom U (CoprodI intPair))) :=
  isSuitableSubgroup_freeProduct_of_partner U (CoprodI intPair)
    isSuitableSubgroup_intPair

end RelHyp
end GGT
end GroupApproximation
