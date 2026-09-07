import GroupApproximation.Manuscript.NonMF.OsinTheorem12NonDegenerate

/-!
# Dahmani--Guirardel--Osin, Theorem 2.35: the C⋆-analytic half, named

`OsinTheorem12NonDegenerate` reduced `cor:regular-nonmf-algebra` to
`SimpleUniqueTraceAtHypEmbedded`, which is DGO's Theorem 2.35 at its own
hypotheses.  This module opens that Prop up along **DGO's own proof**, so that
what remains is named rather than bundled.

## DGO's proof of `(a) ⇒ (d) ∧ (e)`, from §8.3 of the memoir

Their argument, in five steps:

1. `(a) ⇒ (b)`: `K(G) = 1` and a non-degenerate hyperbolically embedded subgroup
   give an infinite cyclic `C = ⟨c⟩ ↪_h G`.  Their Theorem 6.14(c) at `n = 1`.
2. Some `n` makes `F :=` the normal closure of `cⁿ` in `G` **free**.  Their
   Theorem 7.19(e), `Ker(ε) = ∗_λ ∗_{t ∈ T_λ} N_λ^t`; equivalently their
   Corollary 5.4, from the free splitting 5.3(a).
3. `C_G(F) = 1`, by **three** applications of their Proposition 4.33.
4. `F` is free non-abelian, so `C*_r(F)` is simple — **Powers**.
5. Their Lemma 8.15 transfers simplicity from `F` to `G`.

The hyperbolically embedded subgroup is used only to manufacture `F` and to
compute its centraliser.  Every C⋆-analytic step is about `F`, a *free group*,
together with one permanence lemma.  In particular the proof does **not** run a
Powers-type averaging argument on the hyperbolically embedded subgroup, and it
does not pass through inner amenability or a boundary action: DGO's conditions
(b) ICC and (c) not inner amenable sit on a different branch of the equivalence,
proved through a Tarski paradoxical decomposition, and the corollary needs
neither.  Nor is the converse `(d) ∨ (e) ⇒ (a)` needed.

## What this module does

Steps 4 and 5 are independent of steps 1--3, so they are separated here.  The
three C⋆ inputs become three **named classical theorems**, and the whole
group-theoretic residue becomes one named obligation,
`FreeNormalSubgroupAtHypEmbedded`.  `simpleUniqueTraceAtHypEmbedded_of_inputs`
assembles DGO 2.35 from the four.

A smaller Prop with a named gap is worth more than a large Prop nobody can
finish: nothing here proves DGO 2.35, but after this module the citation is four
statable theorems instead of one opaque one, and three of the four are classical
C⋆-algebra facts with no geometric group theory in them at all.

## The unique-trace step, and a thin point in the printed proof

DGO write *"Thus we obtain (e) and (f) by Lemma 8.15"*, where (f) is the unique
trace.  **Their Lemma 8.15 as printed concludes C⋆-simplicity only:**

> **Lemma 8.15 ([2, Theorem 3]).**  If a countable group `G` contains a
> `C*`-simple normal subgroup `N` with trivial centralizer, then `G` is
> `C*`-simple.

`[2]` is C. A. Akemann and T.-Y. Lee, *Some simple `C*`-algebras associated with
free groups*, Indiana Univ. Math. J. **29** (1980), 505--511.  So the unique
trace does not follow from the lemma as DGO quote it.  Rather than state a Prop
asserting what the cited lemma does not say, the unique trace is carried here by
a **separate** named citation, which supplies it outright:

> **Breuillard--Kalantar--Kennedy--Ozawa, Theorem 1.3.**  A discrete group has
> the unique trace property if and only if its amenable radical is trivial.  *In
> particular, every `C*`-simple group has the unique trace property.*

Note carefully what this does and does not say.  It is a remark about the
internal structure of **DGO's proof**, not about the manuscript's citation:
DGO's Theorem 2.35 does assert both (d) and (e), so
`non_mf_groups_exist.tex` citing it for simplicity and uniqueness of the trace
is correct and needs no change.  See the header of `OsinTheorem12NonDegenerate`,
which quotes 2.35 in full and retracts an earlier claim to the contrary.

## The prerequisite the Powers step will meet first

`PowersFreeGroupCStarSimple` is stated for any group that *is* free of rank at
least two, which is how the theorem reads, rather than for `FreeGroup X`.  A
proof will therefore need `C*_r` to transport along a group isomorphism, and
**that functoriality does not exist in this repository**: there is no
`reducedGroupCStar` congruence along a `MulEquiv`.  `IsSimpleCStar` already
transports along a ⋆-isomorphism (`IsSimpleCStar.of_starAlgEquiv`), so what is
missing is exactly the ⋆-isomorphism `C*_r(G) ≃⋆ₐ[ℂ] C*_r(H)` induced by
`G ≃* H`.  That is the first thing to build, and it is reusable well beyond
this lane.

## What the repository already supplies for steps 1--3

* **Step 3 is done.**  DGO's Proposition 4.33 is proved here, unconditionally:
  `GGT.dgoProposition433 : GGT.DGOProposition433.{u}`, in
  `GroupApproximation/GGT/DGOProposition433Finite.lean`.  The centraliser
  computation is the fiddliest group-theoretic step of the whole proof and its
  tool is already available; a future lane should not re-derive it.
* **Step 1 is open, and the name that looks like it is not it.**
  `GGT.DGOTheorem614` is *not* DGO's Theorem 6.14.  It concludes
  `PingPong.FreeRankTwo G` — that `G` contains a free subgroup of rank two —
  which is one weak consequence; its own docstring says it records only what
  Osin's Lemma 5.12 needs and is off the critical path.  Nothing inhabits it.
  Step 1 needs 6.14(a) (existence of `K(G)`) and 6.14(c) at `n = 1` (a
  hyperbolically embedded `H ≅ F₁ × K(G)`), neither of which is present.  Its own
  input, DGO's Corollary 6.12, *is* proved here.
* **Step 2 is open.**  DGO's Theorem 5.3 is proved
  (`Manuscript.NonMF.TheoremCAssembly.dgoTheorem53`), but only clause **(b)**,
  the dichotomy — which is 7.19(d).  Clause **(a)**, the free splitting, is what
  step 2 consumes and is absent; see the note on `HullSC.RotatingQuotient`.
  Nothing in the corpus constructs an `IsVeryRotating` either — it occurs only
  as a hypothesis.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.ReducedGroupCStarTrace

/-! ## "free of rank at least two" -/

/-- **A free group of rank at least two.**  Stated with an explicit free basis
rather than through `IsFreeGroup.Generators`, so that no choice of basis is
buried in the statement and the rank condition is visible as *"the index type
has two distinct elements"*.

This is the hypothesis of Powers' theorem, and it is also what step 2 of DGO's
proof produces: the normal closure of `cⁿ` is a free product of infinitely many
conjugates of `⟨cⁿ⟩ ≅ ℤ`, hence free of infinite rank. -/
def IsFreeOfRankGeTwo (H : Type) [Group H] : Prop :=
  ∃ X : Type, (∃ a b : X, a ≠ b) ∧ Nonempty (FreeGroup X ≃* H)

/-! ## The three C⋆ citations -/

/-- **Powers' theorem.**  The reduced C⋆-algebra of a free group of rank at
least two is simple.

Stated at a group that *is* free, not at `FreeGroup X`, because that is how the
theorem reads and how step 4 of DGO's proof consumes it — there `F` is a normal
subgroup of `G` that happens to be free, not a copy of `FreeGroup X`. -/
def PowersFreeGroupCStarSimple : Prop :=
  ∀ (H : Type) [Group H] [Countable H],
    IsFreeOfRankGeTwo H → IsSimpleCStar (ReducedGroupCStar H)

/-- **Akemann--Lee, Theorem 3**, which Dahmani--Guirardel--Osin quote as their
Lemma 8.15:

> If a countable group `G` contains a `C*`-simple normal subgroup `N` with
> trivial centralizer, then `G` is `C*`-simple.

Breuillard--Kalantar--Kennedy--Ozawa's Theorem 1.4 — *"`G` is `C*`-simple if and
only if both `N` and `C_G(N)` are `C*`-simple"* — is a sharper modern form of
the same fact, and specialises to this one when `C_G(N)` is trivial. -/
def AkemannLeeCStarSimplePermanence : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (N : Subgroup G), N.Normal →
    IsSimpleCStar (ReducedGroupCStar N) →
      Subgroup.centralizer (N : Set G) = ⊥ →
        IsSimpleCStar (ReducedGroupCStar G)

/-- **Breuillard--Kalantar--Kennedy--Ozawa, Theorem 1.3**, second sentence:
*"every `C*`-simple group has the unique trace property."*

This is what supplies conclusion (f) of DGO's Theorem 2.35.  DGO attribute it to
their Lemma 8.15, which as printed concludes simplicity only; see the module
header. -/
def BKKOUniqueTraceOfCStarSimple : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    IsSimpleCStar (ReducedGroupCStar G) →
      HasUniqueTracialState (ReducedGroupCStar G)

/-! ## The group-theoretic residue, as one named obligation -/

/-- **Steps 1--3 of DGO's proof, bundled as the single thing they produce.**

From a countable group with a non-degenerate hyperbolically embedded subgroup
and no nontrivial finite normal subgroup: a normal subgroup that is free of rank
at least two and has trivial centraliser.

This is the whole geometric-group-theory content of DGO's Theorem 2.35, and it
is where the remaining difficulty lives — their Theorem 6.14, their Theorem
7.19(e) (equivalently the free splitting 5.3(a)), and three applications of
Proposition 4.33, the last of which is already proved here. -/
def FreeNormalSubgroupAtHypEmbedded : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    (∃ E : Subgroup G, GGT.IsNonDegenerate E ∧ GGT.IsHypEmbedded G E) →
      HasTrivialFiniteRadical G →
        ∃ N : Subgroup G, N.Normal ∧ IsFreeOfRankGeTwo N ∧
          Subgroup.centralizer (N : Set G) = ⊥

/-! ## The slice, and the assembly -/

/-- **Steps 4 and 5 of DGO's proof, in isolation.**

A countable group with a free normal subgroup of rank at least two and trivial
centraliser has simple reduced C⋆-algebra with a unique tracial state.

Nothing geometric appears: this is Powers, then Akemann--Lee, then
Breuillard--Kalantar--Kennedy--Ozawa. -/
theorem simpleUniqueTrace_of_free_normal_subgroup
    (hPowers : PowersFreeGroupCStarSimple)
    (hAL : AkemannLeeCStarSimplePermanence)
    (hBKKO : BKKOUniqueTraceOfCStarSimple)
    (G : Type) [Group G] [Countable G] (N : Subgroup G) (hnorm : N.Normal)
    (hfree : IsFreeOfRankGeTwo N)
    (hcent : Subgroup.centralizer (N : Set G) = ⊥) :
    IsSimpleCStar (ReducedGroupCStar G) ∧
      HasUniqueTracialState (ReducedGroupCStar G) := by
  -- Step 4: `F` is free of rank ≥ 2, so `C*_r(F)` is simple.
  have hN : IsSimpleCStar (ReducedGroupCStar N) := hPowers N hfree
  -- Step 5: transfer to `G` along the normal subgroup with trivial centraliser.
  have hG : IsSimpleCStar (ReducedGroupCStar G) := hAL G N hnorm hN hcent
  exact ⟨hG, hBKKO G hG⟩

/-- **DGO's Theorem 2.35, assembled from four named statements.**

Three are classical C⋆-algebra theorems with no geometric group theory in them;
the fourth, `FreeNormalSubgroupAtHypEmbedded`, is the entire geometric residue.
This is the shape the citation now has. -/
theorem simpleUniqueTraceAtHypEmbedded_of_inputs
    (hPowers : PowersFreeGroupCStarSimple)
    (hAL : AkemannLeeCStarSimplePermanence)
    (hBKKO : BKKOUniqueTraceOfCStarSimple)
    (hGroup : FreeNormalSubgroupAtHypEmbedded) :
    SimpleUniqueTraceAtHypEmbedded := by
  intro G instG instC hemb hrad
  letI := instG
  letI := instC
  obtain ⟨N, hnorm, hfree, hcent⟩ := hGroup G hemb hrad
  exact simpleUniqueTrace_of_free_normal_subgroup hPowers hAL hBKKO G N hnorm
    hfree hcent

/-- **`cor:regular-nonmf-algebra`'s simplicity and unique-trace clauses, in
terms of the four.**  Composing with `dgoTheorem235Printed_of_hypEmbedded`,
whose bridge is the proved Osin Theorem 1.2, gives the printed form. -/
theorem dgoTheorem235Printed_of_inputs
    (hPowers : PowersFreeGroupCStarSimple)
    (hAL : AkemannLeeCStarSimplePermanence)
    (hBKKO : BKKOUniqueTraceOfCStarSimple)
    (hGroup : FreeNormalSubgroupAtHypEmbedded) : DGOTheorem235Printed :=
  dgoTheorem235Printed_of_hypEmbedded
    (simpleUniqueTraceAtHypEmbedded_of_inputs hPowers hAL hBKKO hGroup)

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms simpleUniqueTrace_of_free_normal_subgroup
#audit_axioms simpleUniqueTraceAtHypEmbedded_of_inputs
#audit_axioms dgoTheorem235Printed_of_inputs
