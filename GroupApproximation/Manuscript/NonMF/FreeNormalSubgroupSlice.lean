import GroupApproximation.Manuscript.NonMF.DGOTheorem235Slice
import GroupApproximation.GGT.HypEmbeddedCentralizer

/-!
# The geometric residue of DGO 2.35, opened along their steps 1 to 3

`DGOTheorem235Slice` cut Dahmani--Guirardel--Osin's Theorem 2.35 down to three
classical C⋆-citations and one geometric obligation,
`FreeNormalSubgroupAtHypEmbedded`: a countable group with a non-degenerate
hyperbolically embedded subgroup and trivial finite radical has a normal
subgroup that is free of rank at least two **and has trivial centraliser**.

That obligation is DGO's steps 1 to 3.  This module opens it along those steps:

1. **Step 1** — their Theorem 6.14(c) at `n = 1`, packaged with their Theorem
   6.8: an element `c` of infinite order whose elementary closure `E(c)` is
   hyperbolically embedded and proper.  `LoxodromicHypEmbeddedClosure`.
2. **Step 2** — their Theorem 7.19(e), equivalently the free splitting 5.3(a):
   for some `n`, the normal closure of `cⁿ` is free of rank at least two.
   `FreeNormalClosureOfPower`.
3. **Step 3** — the centraliser computation, which is **proved**, in
   `GGT/HypEmbeddedCentralizer.lean`, out of the repository's own
   `GGT.dgoProposition433`.  The header of `DGOTheorem235Slice` predicted that
   a later lane would do exactly this and asked that it not be re-derived; this
   is that lane.

`freeNormalSubgroupAtHypEmbedded_of_inputs` assembles the three.  So after this
module the geometric residue of DGO 2.35 is two named theorems of their memoir
rather than one unnamed obligation, and the third step is gone.

## Why step 1 is phrased through the elementary closure

Step 3 needs a hyperbolically embedded subgroup that contains the centraliser of
the normal subgroup, and the centraliser of a normal subgroup containing `c`
lies in `E(c)` and in nothing smaller that is visible without geometry.  DGO's
own step 1 produces `⟨c⟩ ↪_h G`; upgrading that to `E(c) ↪_h G` is their Theorem
6.8, which `GGT/WPDElementaryEmbedding` reduces to one named geometric
proposition.  Packaging the two into a single obligation keeps the interface
honest: what step 2 and step 3 both consume is `E(c) ↪_h G`.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` through DGO 2.35; certifies no
printed sentence on its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## Step 1 -/

/-- **Dahmani--Guirardel--Osin, Theorem 6.14(c) at `n = 1`, with their Theorem
6.8.**

From a countable group with a non-degenerate hyperbolically embedded subgroup
and no nontrivial finite normal subgroup: an element `c` of infinite order whose
elementary closure is hyperbolically embedded, and is proper.

DGO's 6.14(c) produces a hyperbolically embedded `H ≅ ℤ × K(G)`, which is `⟨c⟩`
when `K(G) = 1`; their 6.8 replaces `⟨c⟩` by the maximal elementary subgroup
`E(c)` containing it.  Properness is the non-degeneracy: a hyperbolically
embedded subgroup equal to the whole group is the degenerate case. -/
def LoxodromicHypEmbeddedClosure : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    (∃ E : Subgroup G, IsNonDegenerate E ∧ IsHypEmbedded G E) →
      HasTrivialFiniteRadical G →
        ∃ c : G, IsHypEmbedded G (elementaryClosure c) ∧
          (∃ a : G, a ∉ elementaryClosure c) ∧
            ∀ k : ℤ, k ≠ 0 → c ^ k ≠ 1

/-! ## Step 2 -/

/-- **Dahmani--Guirardel--Osin, Theorem 7.19(e)**, equivalently the free
splitting of their Theorem 5.3(a):

for an element `c` of infinite order with `E(c) ↪_h G`, some power `cⁿ` has free
normal closure — their proof exhibits it as the free product of infinitely many
conjugates of `⟨cⁿ⟩`, so it is free of rank at least two. -/
def FreeNormalClosureOfPower : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (c : G),
    IsHypEmbedded G (elementaryClosure c) →
      (∀ k : ℤ, k ≠ 0 → c ^ k ≠ 1) →
        ∃ n : ℕ, 0 < n ∧
          IsFreeOfRankGeTwo (Subgroup.normalClosure ({c ^ n} : Set G))

/-! ## The assembly -/

/-- **The geometric residue of DGO 2.35 from steps 1 and 2 alone.**

Step 3, the centraliser computation, is discharged by
`GGT.centralizer_eq_bot_of_isHypEmbedded_elementaryClosure`, which runs on the
proved Proposition 4.33. -/
theorem freeNormalSubgroupAtHypEmbedded_of_inputs
    (h1 : LoxodromicHypEmbeddedClosure) (h2 : FreeNormalClosureOfPower) :
    FreeNormalSubgroupAtHypEmbedded := by
  intro G instG instC hemb hrad
  letI := instG
  letI := instC
  obtain ⟨c, hE, ⟨a, ha⟩, hinf⟩ := h1 G hemb hrad
  obtain ⟨n, hn, hfree⟩ := h2 G c hE hinf
  have hnz : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hclosure : elementaryClosure (c ^ n) = elementaryClosure c := by
    rw [show c ^ n = c ^ ((n : ℕ) : ℤ) from (zpow_natCast c n).symm,
      elementaryClosure_zpow c hnz]
  refine ⟨Subgroup.normalClosure ({c ^ n} : Set G),
    Subgroup.normalClosure_normal, hfree, ?_⟩
  refine centralizer_eq_bot_of_isHypEmbedded_elementaryClosure
    Subgroup.normalClosure_normal (c := c ^ n) (a := a)
      (Subgroup.subset_normalClosure rfl) ?_ ?_ hrad
  · rw [hclosure]
    exact hE
  · rw [hclosure]
    exact ha

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms freeNormalSubgroupAtHypEmbedded_of_inputs
