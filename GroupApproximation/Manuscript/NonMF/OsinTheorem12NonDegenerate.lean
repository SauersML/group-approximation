import GroupApproximation.GGT.AH3GeodesicCayley
import GroupApproximation.GGT.DGOTheorem442Proof
import GroupApproximation.Manuscript.NonMF.RegularNonMFAlgebra

/-!
# Osin's Theorem 1.2, in the direction `cor:regular-nonmf-algebra` uses it

`non_mf_groups_exist.tex`, the proof of `cor:regular-nonmf-algebra`, opens:

> The group `Q` is countable, torsion-free, and acylindrically hyperbolic, so it
> contains a non-degenerate hyperbolically embedded subgroup [Osin, Theorem 1.2]
> and has no nontrivial finite normal subgroup.

That sentence is the only use of Osin's Theorem 1.2 in the corollary, and it is
the implication `(AH₁) ⇒ (AH₄)` of that theorem.  **It is proved here, not
cited.**

## Why this is not `GGT.OsinTheorem12`

The repository already carries a proposition named `GGT.OsinTheorem12`, and it
is the *other* implication:

```
def OsinTheorem12 : Prop :=
  ∀ (G : Type u) [Group G], AH3Data.{u, v} G → ¬ IsVirtuallyCyclic G →
    IsAcylindricallyHyperbolic G
```

that is `(AH₃) ⇒ (AH₁)`, which is what Minasyan--Osin's tree criterion consumes.
Reading the identifier rather than the binder would suggest the corollary's
sentence is already available; it is not.  The direction the corollary needs
runs the opposite way, from acylindrical hyperbolicity *to* a hyperbolically
embedded subgroup, and it is assembled below from four landed results.

## What is proved

* `exists_isNonDegenerate_isHypEmbedded` — **Osin, Theorem 1.2, `(AH₁) ⇒ (AH₄)`,
  with no hypothesis beyond the class**: an acylindrically hyperbolic group
  contains a non-degenerate hyperbolically embedded subgroup.  The four inputs,
  all landed and complete, with no axioms beyond `propext`,
  `Classical.choice` and `Quot.sound`:

  1. `GGT.exists_ah3Data_of_isAcylindricallyHyperbolic` — `(AH₁) ⇒ (AH₃)`, on the
     genuine geodesic realisation of the Cayley graph;
  2. `HullSC.not_isVirtuallyCyclic_of_actsNonElementarily` applied to the
     `ActsNonElementarily` clause that `IsAcylindricallyHyperbolic` already
     carries — this discharges the `¬ IsVirtuallyCyclic` hypothesis of
     `(AH₃)` from the class itself, so it costs the corollary nothing;
  3. `GGT.Elementary.dgoTheorem68_of_projection_unconditional` applied to
     `GGT.Elementary.dgoTheorem442_unconditional` — `(AH₃) ⇒ (AH₄)`,
     Dahmani--Guirardel--Osin's Corollary 2.9, *unconditional* in this
     repository through the proof of their Theorem 4.42;
  4. `GGT.infinite_of_mem_of_isLoxodromic` — the infinitude half of
     non-degeneracy, from the loxodromic element `AH3Data` records.

  Properness, the other half of `GGT.IsNonDegenerate`, is what `DGOTheorem68`
  returns directly.

* `osinTheorem12Printed_unconditional` — the same statement packaged as the
  named Prop `OsinTheorem12Printed`, so that a census row citing "Osin,
  Theorem 1.2" has a closed endpoint to name.

* `dgoTheorem235Printed_of_hypEmbedded` — the bridge that the docstring of
  `DGOTheorem235Printed` previously asserted rather than proved.

## The universe

`GGT.Elementary.dgoTheorem442_unconditional` is proved at `DGOTheorem442.{0, 0}`
only, so `(AH₃) ⇒ (AH₄)` is available here at `Type 0` only.  That is exactly
the quantifier of `DGOTheorem235Printed` and `GerasimovaOsinTheorem11Printed`,
which range over `∀ (G : Type)`, so nothing is lost at the corollary.

## A correction to the docstring of `RegularNonMFAlgebra`

That module says of both C⋆-side citations:

> Osin's Theorem 1.2 is the step that licenses that form: it turns those
> hypotheses into DGO's own, the existence of a non-degenerate hyperbolically
> embedded subgroup.  It is not a separate Prop here because this module has no
> vocabulary for *hyperbolically embedded*.

Two things are now different.

* The vocabulary exists — `GGT.IsHypEmbedded` and `GGT.IsNonDegenerate` — and
  the step is *proved*, so the fold is no longer an assertion.
  `dgoTheorem235Printed_of_hypEmbedded` derives the printed form from the form stated
  at a non-degenerate hyperbolically embedded subgroup.
* The fold is unnecessary for **Gerasimova--Osin**.  Their Theorem 1.1 reads,
  verbatim from arXiv:1910.14524v2:

  > **Theorem 1.1.** Let `G₁, …, G_k` be acylindrically hyperbolic groups with
  > `K(G_i) = {1}` for all `1 ≤ i ≤ k`.  Then `sr(C*_r(G₁ × ⋯ × G_k)) = 1`.  In
  > particular, the reduced `C*`-algebra of any acylindrically hyperbolic group
  > with trivial finite radical has stable rank `1`.

  Their hypotheses are acylindrical hyperbolicity and a trivial finite radical
  — already the hypotheses of `GerasimovaOsinTheorem11Printed`.  No
  hyperbolically embedded subgroup appears in their statement, so Osin's
  Theorem 1.2 is not folded into that Prop and never was.

## Dahmani--Guirardel--Osin, Theorem 2.35, verbatim

The citation is stated below at exactly the hypotheses of its source, which
reads (arXiv:1111.7048v5; the memoir numbers it again as Theorem 8.14):

> **Theorem 2.35 (Theorem 8.14).**  Suppose that a group `G` contains a
> non-degenerate hyperbolically embedded subgroup.  Then the following
> conditions are equivalent.
> * (a) `G` has no nontrivial finite normal subgroups.
> * (b) `G` is ICC.
> * (c) `G` is not inner amenable.
>
> If, in addition, `G` is countable, the above conditions are also equivalent to
> * (d) The reduced `C*`-algebra of `G` is simple.
> * (e) The reduced `C*`-algebra of `G` has a unique normalized trace.

`SimpleUniqueTraceAtHypEmbedded` is `(a) ⇒ (d) ∧ (e)` for countable `G`, which
is the implication the corollary consumes.  The hypothesis of the theorem is a
non-degenerate hyperbolically embedded subgroup, **not** acylindrical
hyperbolicity — which is precisely why the printed proof invokes Osin's
Theorem 1.2 first, and why `dgoTheorem235Printed_of_hypEmbedded` is the bridge
it describes rather than a restatement.

A note against a false correction, because the repository twice recorded one.
`research/artifacts/mf-radical-linear-certificate-2026-09-07.md` §4.1 claims
that DGO 2.35 "identifies the amenable radical … with its finite radical" and
that Breuillard--Kalantar--Kennedy--Ozawa's Theorem 1.4 is needed to reach the
unique trace.  Both clauses are false: DGO 2.35 is the equivalence quoted
above, and BKKO's Theorem 1.4 reads

> **Theorem 1.4.**  Let `G` be a discrete group and let `N ≤ G` be a normal
> subgroup.  Then `G` is `C*`-simple if and only if both `N` and `C_G(N)` are
> `C*`-simple.  In particular, `C*`-simplicity is closed under extension.

Gerasimova and Osin cite the two together because their own theorem is about
*products* `G₁ × ⋯ × G_k`: DGO 2.35 handles each factor and BKKO 1.4 passes to
the product.  The corollary here needs only `k = 1`, so BKKO is no part of its
chain, and the manuscript's citation of DGO Theorem 2.35 alone is correct.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.ReducedGroupCStarTrace

universe u

/-! ## Osin's Theorem 1.2, `(AH₁) ⇒ (AH₄)` -/

/-- **Osin, *Acylindrically hyperbolic groups*, Theorem 1.2, the implication
`(AH₁) ⇒ (AH₄)`**, which is the one the proof of `cor:regular-nonmf-algebra`
uses:

> The group `Q` is countable, torsion-free, and acylindrically hyperbolic, so it
> contains a non-degenerate hyperbolically embedded subgroup.

Proved, not assumed.  `¬ IsVirtuallyCyclic` — the hypothesis `DGOTheorem68` asks
for — is not a hypothesis here: it is extracted from the `ActsNonElementarily`
clause that `IsAcylindricallyHyperbolic` already carries, by
`HullSC.not_isVirtuallyCyclic_of_actsNonElementarily`. -/
theorem exists_isNonDegenerate_isHypEmbedded (G : Type) [Group G]
    [hG : IsAcylindricallyHyperbolic G] :
    ∃ E : Subgroup G, GGT.IsNonDegenerate E ∧ GGT.IsHypEmbedded G E := by
  -- `(AH₁) ⇒ (AH₃)`.
  obtain ⟨D⟩ := GGT.exists_ah3Data_of_isAcylindricallyHyperbolic G
  letI := D.metricSpace
  letI := D.mulAction
  -- "`G` is not virtually cyclic": from the non-elementarity clause of `(AH₁)`.
  obtain ⟨A, δ, hδ, hacy, hne⟩ := hG.out
  have hnvc : ¬ GGT.IsVirtuallyCyclic G :=
    HullSC.not_isVirtuallyCyclic_of_actsNonElementarily
      (isIsometricAction_cayley A) hne
  -- `(AH₃) ⇒ (AH₄)`: Dahmani--Guirardel--Osin's Corollary 2.9, unconditional.
  have h68 : GGT.DGOTheorem68.{0, 0} :=
    GGT.Elementary.dgoTheorem68_of_projection_unconditional
      GGT.Elementary.dgoTheorem442_unconditional
  obtain ⟨E, hmem, hproper, hemb⟩ := h68 G D hnvc
  -- Non-degeneracy: proper from the citation, infinite from loxodromy.
  exact ⟨E, ⟨hproper, GGT.infinite_of_mem_of_isLoxodromic D.loxodromic hmem⟩, hemb⟩

/-- **Osin, Theorem 1.2, as a named Prop** — the closed endpoint a census row
citing that theorem can name.  Unlike the literature propositions of this
development it is inhabited, by `osinTheorem12Printed_unconditional`. -/
def OsinTheorem12Printed : Prop :=
  ∀ (G : Type) [Group G], IsAcylindricallyHyperbolic G →
    ∃ E : Subgroup G, GGT.IsNonDegenerate E ∧ GGT.IsHypEmbedded G E

/-- **Osin's Theorem 1.2 is not a debt of this manuscript.** -/
theorem osinTheorem12Printed_unconditional : OsinTheorem12Printed := by
  intro G instG hah
  letI := instG
  letI := hah
  exact exists_isNonDegenerate_isHypEmbedded G

/-! ## The C⋆-side citation, stated at its source hypothesis -/

/-- **Dahmani--Guirardel--Osin, Theorem 2.35**, at its own hypotheses: a
countable group with a non-degenerate hyperbolically embedded subgroup and no
nontrivial finite normal subgroup has simple reduced C⋆-algebra with a unique
tracial state.

This is the implication `(a) ⇒ (d) ∧ (e)` of the equivalence quoted in the
module header, and it is the whole of what `cor:regular-nonmf-algebra` consumes;
DGO's conditions (b) ICC and (c) not inner amenable are not used and are not
asked for here.

The hypothesis is the hyperbolically embedded subgroup rather than acylindrical
hyperbolicity because that is what the source asks and what the printed proof
produces before quoting the theorem — `exists_isNonDegenerate_isHypEmbedded` now
supplies it.  Stating it this way makes the Prop *weaker* than one asking only
for acylindrical hyperbolicity, so the derivation below is the load-bearing
direction. -/
def SimpleUniqueTraceAtHypEmbedded : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    (∃ E : Subgroup G, GGT.IsNonDegenerate E ∧ GGT.IsHypEmbedded G E) →
      HasTrivialFiniteRadical G →
        IsSimpleCStar (ReducedGroupCStar G) ∧
          HasUniqueTracialState (ReducedGroupCStar G)

/-- **The fold, proved.**  `DGOTheorem235Printed` states the citation at
acylindrical hyperbolicity; `SimpleUniqueTraceAtHypEmbedded` states it at the
hypothesis Dahmani--Guirardel--Osin themselves use.  Osin's Theorem 1.2 is what
carries one to the other, and here it is the *theorem*
`exists_isNonDegenerate_isHypEmbedded` rather than a docstring remark. -/
theorem dgoTheorem235Printed_of_hypEmbedded
    (h : SimpleUniqueTraceAtHypEmbedded) : DGOTheorem235Printed := by
  intro G instG instC instAH hrad
  letI := instG
  letI := instC
  letI := instAH
  exact h G (exists_isNonDegenerate_isHypEmbedded G) hrad

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms exists_isNonDegenerate_isHypEmbedded
#audit_axioms osinTheorem12Printed_unconditional
#audit_axioms dgoTheorem235Printed_of_hypEmbedded
