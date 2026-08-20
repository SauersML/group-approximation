import GroupApproximation.Higman.Operations
import GroupApproximation.Higman.RopeTorsion
import GroupApproximation.Higman.EmbeddingTheorem
import GroupApproximation.Higman.BridgeTorsion

/-!
# Higman's Theorem 4, and what is left of it

Higman's Theorem 4 says: a subset `B` of the sequence space is recursively
enumerable exactly when `A_B` is benign in `F₃`.  The direction the embedding
theorem needs is `⟸ of r.e.`, and it is his Sections 2 and 4 together:

* **Section 2** --- every recursively enumerable subset is built from `Z` and
  `S` by the nine operations (`HigmanTheoremThree` below);
* **Section 4** --- the family of subsets with benign subgroup contains `Z`
  and `S` and is closed under the nine operations
  (`Higman.OperationClosures`, of which three are proved);

and then

* **Section 5** --- the transport from the coded subgroups `A_B` to arbitrary
  recursively enumerable normal subgroups of free groups of finite rank
  (`TransportSectionFive` below).

`reBenignTF_of_inputs` composes the three into `Higman.REBenignTF`, which by
`Higman.RopeTorsion` and `Higman.EmbeddingTheorem` is everything Higman's
embedding theorem owes.  Nothing else is needed: the induction over the nine
operations is `benignTF_of_higmanGenerated`, and it is proved.

## Recursive enumerability on the sequence space

A sequence is coded by a finite list of index/value pairs, which is a
`Primcodable` datum, and a subset of the sequence space is recursively
enumerable when the set of codes of its members is.  The coding is surjective,
so nothing is lost.
-/

namespace GroupApproximation
namespace Higman

/-! ## 1.  Coding the sequence space -/

/-- The sequence coded by a list of index/value pairs. -/
noncomputable def seqOfList (l : List (ℤ × ℤ)) : E :=
  (l.map fun p => Finsupp.single p.1 p.2).sum

/-- The coding is onto: every finitely supported sequence is a finite sum of
single-index sequences. -/
theorem seqOfList_surjective : Function.Surjective seqOfList := by
  classical
  intro f
  refine ⟨(f.support.sort (· ≤ ·)).map (fun i => (i, f i)), ?_⟩
  unfold seqOfList
  rw [List.map_map]
  have hperm : ((f.support.sort (· ≤ ·)).map
      (fun i => Finsupp.single i (f i))).sum
      = ∑ i ∈ f.support, Finsupp.single i (f i) := by
    rw [Finset.sum_eq_multiset_sum]
    refine List.Perm.sum_eq ?_
    exact (Finset.sort_perm_toList _ _).map _
  show ((f.support.sort (· ≤ ·)).map
    ((fun p : ℤ × ℤ => Finsupp.single p.1 p.2) ∘ (fun i => (i, f i)))).sum = f
  rw [show ((fun p : ℤ × ℤ => Finsupp.single p.1 p.2) ∘ (fun i => (i, f i)))
      = (fun i : ℤ => Finsupp.single i (f i)) from rfl, hperm]
  exact Finsupp.sum_single f

/-- A subset of the sequence space is recursively enumerable when the set of
codes of its members is. -/
def REset (B : Set E) : Prop :=
  REPred (fun l : List (ℤ × ℤ) => seqOfList l ∈ B)

/-! ## 2.  The two remaining halves of Theorem 4, and the transport -/

/-- **Input: Higman's Section 2.**  Every recursively enumerable subset of the
sequence space is built from `Z` and `S` by the nine operations.

**Nothing inhabits this structure.** -/
structure HigmanTheoremThree where
  /-- Recursively enumerable sets are Higman-generated. -/
  generated : ∀ B : Set E, REset B → Seq.HigmanGenerated B

/-- **Input: Higman's Section 5.**  The passage from the coded subgroups `A_B`
to arbitrary recursively enumerable normal subgroups of free groups of finite
rank.

**Nothing inhabits this structure.** -/
structure TransportSectionFive where
  /-- Benignness of every coded subgroup gives benignness of every recursively
  enumerable normal subgroup. -/
  transport : (∀ B : Set E, REset B → BenignTF (Seq.ASub B)) → REBenignTF

/-! ## 3.  The composite -/

/-- **Higman's Theorem 4, from its two halves.** -/
theorem benignTF_ASub_of_re (h₁ : OperationClosures) (h₂ : HigmanTheoremThree)
    (B : Set E) (hB : REset B) : BenignTF (Seq.ASub B) :=
  benignTF_of_higmanGenerated h₁ (h₂.generated B hB)

/-- **What Higman's embedding theorem owes, assembled.**  The six remaining
operation closures, the base case `S`, Section 2 and Section 5 give
`REBenignTF` --- and with it, through `Higman.torsionPreservation_of_reBenignTF`
and `Higman.fpOvergroup_of_fgRecursive`, Higman's embedding theorem with
Chiodo's torsion clause. -/
def reBenignTF_of_inputs (h₁ : OperationClosures) (h₂ : HigmanTheoremThree)
    (h₃ : TransportSectionFive) : REBenignTF :=
  h₃.transport (benignTF_ASub_of_re h₁ h₂)

/-- **The whole chain to Chiodo Theorem 3.10.**  Five inputs, and everything
between them is proved in this repository. -/
theorem nonempty_universalTorsionFreeHost_of_five (h₁ : OperationClosures)
    (h₂ : HigmanTheoremThree) (h₃ : TransportSectionFive)
    (h₄ : BridgeRecursive) (h₅ : AbsorberRecursivePresentation) :
    Nonempty FournierFacioUniversal.UniversalTorsionFreeHost :=
  nonempty_universalTorsionFreeHost_of_three
    (countableToFG_of_input h₄)
    (torsionPreservation_of_reBenignTF (reBenignTF_of_inputs h₁ h₂ h₃)) h₅

end Higman
end GroupApproximation
