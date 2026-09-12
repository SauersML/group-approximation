import GroupApproximation.Manuscript.NonMF.DGOTheorem235Slice
import GroupApproximation.Manuscript.NonMF.DGO235FromPowersProperty

/-!
# Dahmani--Guirardel--Osin's own route to Theorem 2.35, with one citation left

`Manuscript/NonMF/DGOTheorem235Slice` transcribes DGO's proof faithfully and
lands on three classical C⋆ citations — Powers, Akemann--Lee,
Breuillard--Kalantar--Kennedy--Ozawa — plus one group-theoretic residue.  This
module runs the same proof through the averaging chain instead, and two of the
three C⋆ citations disappear:

* Powers' theorem becomes `PowersPropertyFreeGroup`, a statement about
  partitions of a free group with no analysis in it, because
  `Analysis/PowersAveragingFromPowersProperty` proves the averaging estimate
  from Powers' combinatorial condition;
* Breuillard--Kalantar--Kennedy--Ozawa is **not needed at all**, because
  `Analysis/PowersAveragingUniqueTrace` gets the unique trace from the same
  estimate that gives simplicity;
* Akemann--Lee stays, but in the *averaging* form
  `AkemannLeeAveragingTransfer`, which is what the chain actually consumes.

## Why Akemann--Lee is not restated as a transfer of Powers' property

That would be the natural guess and it appears to be **wrong**.  The literature
does not list the Powers property as a permanence property of normal subgroups
with trivial centraliser; it introduces a *new class* for exactly that
hypothesis — a group is an **ultraweak Powers group** when it contains a normal
weak Powers subgroup with trivial centraliser — and proves C⋆-simplicity for
that class directly (Bédos; Bekka--de la Harpe, *Groups with simple reduced
C\*-algebras*, Expo. Math. **18** (2000) 215--230).  De la Harpe's survey
(arXiv:math/0509450), whose Definition 9 is `PowersProperty` verbatim, states no
such transfer either.

The obstruction is clause two, not clause one.  For `n` pairwise disjoint
translates the set `D` must be `1/n`-small, so `C` is co-small and therefore
meets almost every coset of `N`; and left translation by an element outside `N`
permutes those cosets with no fixed point, so `f C` and `C` are then compared
across different cosets with no room left to separate them.

So the honest statement is the one below, at the level of the estimate, where
Akemann--Lee's theorem does apply.

## Manuscript status

Reduction step for `cor:regular-nonmf-algebra`; certifies no printed sentence on
its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.ReducedGroupCStarTrace

/-! ## The two inputs -/

/-- **Powers' theorem at the combinatorial level.**  A group that is free of
rank at least two has Powers' property, in the sense of Definition 9 of de la
Harpe's survey, which is `ReducedGroupCStarTrace.PowersProperty` verbatim.

This is what `PowersFreeGroupCStarSimple` should have been: the same theorem
before it is converted into a statement about C⋆-algebras, so that it can be
proved by counting reduced words.  It is a theorem of the literature — de la
Harpe and Préaux, arXiv:0909.3528, Item 8(iv): *"torsion-free Gromov-hyperbolic
groups are Powers groups; in particular, non-abelian free groups are Powers
groups"* — so this Prop is a genuine target and not a wish. -/
def PowersPropertyFreeGroup : Prop :=
  ∀ (H : Type) [Group H], IsFreeOfRankGeTwo H → PowersProperty H

/-- **Akemann--Lee, Theorem 3, in averaging form.**  Dahmani, Guirardel and
Osin quote their theorem as Lemma 8.15:

> If a countable group `G` contains a `C*`-simple normal subgroup `N` with
> trivial centralizer, then `G` is `C*`-simple.

Stated here at the averaging estimate rather than at simplicity.  The two are
the same statement: Haagerup's theorem (*A new look at C\*-simplicity and the
unique trace property of a group*) makes the averaging property equivalent to
C⋆-simplicity, so this Prop is Akemann--Lee and nothing more.  Carrying it in
averaging form is what lets the *unique trace* come out with the simplicity,
which is why `BKKOUniqueTraceOfCStarSimple` does not appear in this module. -/
def AkemannLeeAveragingTransfer : Prop :=
  ∀ (G : Type) [Group G] (N : Subgroup G), N.Normal →
    Subgroup.centralizer (N : Set G) = ⊥ →
      PowersAveragingEstimate N → PowersAveragingEstimate G

/-! ## The composition -/

/-- **A free normal subgroup of rank at least two with trivial centraliser gives
the averaging estimate.**  Steps 4 and 5 of DGO's proof, with Powers' theorem
taken at the combinatorial level. -/
theorem powersAveragingEstimate_of_freeNormalSubgroup
    (hFree : PowersPropertyFreeGroup) (hTransfer : AkemannLeeAveragingTransfer)
    (G : Type) [Group G] (N : Subgroup G) (hnorm : N.Normal)
    (hfreeN : IsFreeOfRankGeTwo N)
    (hcent : Subgroup.centralizer (N : Set G) = ⊥) :
    PowersAveragingEstimate G :=
  hTransfer G N hnorm hcent
    (powersAveragingEstimate_of_powersProperty (↥N) (hFree (↥N) hfreeN))

/-- **DGO's Theorem 2.35 at its own hypotheses, from two inputs.**

`FreeNormalSubgroupAtHypEmbedded` is the geometric residue already named in
`DGOTheorem235Slice`.  Of the three C⋆ citations that module needs, one is
replaced by a combinatorial statement, one is kept in averaging form, and the
third is gone. -/
theorem simpleUniqueTraceAtHypEmbedded_of_powersInputs
    (hFree : PowersPropertyFreeGroup) (hTransfer : AkemannLeeAveragingTransfer)
    (hGroup : FreeNormalSubgroupAtHypEmbedded) :
    SimpleUniqueTraceAtHypEmbedded := by
  intro G instG instC hemb hrad
  letI := instG
  letI := instC
  obtain ⟨N, hnorm, hfreeN, hcent⟩ := hGroup G hemb hrad
  exact simpleUniqueTrace_of_powersAveragingEstimate G
    (powersAveragingEstimate_of_freeNormalSubgroup hFree hTransfer G N hnorm
      hfreeN hcent)

/-- **The printed citation, along DGO's own route, without
Breuillard--Kalantar--Kennedy--Ozawa.** -/
theorem dgoTheorem235Printed_of_powersInputs
    (hFree : PowersPropertyFreeGroup) (hTransfer : AkemannLeeAveragingTransfer)
    (hGroup : FreeNormalSubgroupAtHypEmbedded) : DGOTheorem235Printed :=
  dgoTheorem235Printed_of_hypEmbedded
    (simpleUniqueTraceAtHypEmbedded_of_powersInputs hFree hTransfer hGroup)

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms powersAveragingEstimate_of_freeNormalSubgroup
#audit_axioms simpleUniqueTraceAtHypEmbedded_of_powersInputs
#audit_axioms dgoTheorem235Printed_of_powersInputs
