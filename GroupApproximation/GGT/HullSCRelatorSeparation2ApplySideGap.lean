import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyIface
import GroupApproximation.GGT.HullSCRelatorSeparation2Span

/-!
# The same-side exclusion, as stated, is false

Item 3 of the Ledger is "no two distinct components of one long side are
connected to each other".  What the chain actually carries is stronger, and the
difference is fatal: the exclusion is quantified over every index `i'` of the
side rather than over the component STARTS.

At `i' = i + 1` it excludes the span of the matched component itself.  That span
is the value of the letter at `i`, which is a `lam`-letter --- that is what
`IsComp lam q i (i + 1)` says --- and the value of an admissible `lam`-letter
lies in `H lam`.  So the exclusion asserts of a member of `H lam` that it is not
one, and no side of any polygon can satisfy it.

`not_sideExclusion_of_isComp` is that, with the witness written down.  It needs
only what the matching step already has in hand: the component, and the
admissibility of the side's letters.

## What this costs

Everything above it is conditional on a hypothesis nothing satisfies, so the
chain is vacuous until the exclusion is repaired.  The endpoint
`HullSC.hullRelatorStatement₂_of_inputs` is not wrong; it is empty.

## The repair, now carried out

The exclusion is consumed in exactly two places, and both had more in hand than
they used.  `HullSC.cross_of_notSameSide` destructures the same-side disjunct of
`GGT.OsinComponents.exists_other_component_of_deep_six` and DISCARDS its
`IsCompStart` clause before applying the exclusion; `innermost_of_sideExclusions`
and `otherArc_of_sideExclusions` take an `IsCompStart` hypothesis and apply the
exclusion without it.  So the repair is to carry that clause into the exclusion:

    ∀ i' : ℕ, i' ≤ q.length → i' ≠ i →
      IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i') →
        (vertex 1 q i)⁻¹ * vertex 1 q i' ∉ D.fam lam

which is what item 3 says in words, and which `i' = i + 1` does not satisfy:
adjacent letters of one index lie in ONE component, so `i + 1` starts no
component when `i` does.  Both consumers go through unchanged --- they now pass
the clause they were discarding --- and the theorem below stands as the record
of why the clause is not decoration.

Everything above the interface carries it: `MatchedPairOutput`,
`DeepMatchOutput`, the four closers, the piece-level theorems, the four-way, and
`hexcl` in the composition, which is the one a caller has to satisfy.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section SideGap

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The same-side exclusion, quantified over every index, is refuted by the
matched component itself.** -/
theorem not_sideExclusion_of_isComp (D : GGT.RelGenSet G Λ) (lam : Λ)
    {q : List (GGT.RelLetter G Λ)} {i : ℕ}
    (hcomp : GGT.OsinComponents.IsComp lam q i (i + 1))
    (hlet : ∀ x ∈ q, D.IsLetter x) :
    ¬ (∀ i' : ℕ, i' ≤ q.length → i' ≠ i →
      (GGT.OsinComponents.vertex (1 : G) q i)⁻¹ *
        GGT.OsinComponents.vertex (1 : G) q i' ∉ D.fam lam) := by
  intro hex
  obtain ⟨hik, hkl, hcomps, -, -⟩ := hcomp
  have hi : i < q.length := by omega
  have hget : q[i]? = some (q[i]'hi) := List.getElem?_eq_getElem hi
  have hspan := span_eq_val_of_getElem? (v := (1 : G)) hget
  have hlam : (q[i]'hi).IsCompOf lam := hcomps i (le_refl i) (by omega) hi
  have hval : (q[i]'hi).val ∈ D.fam lam :=
    GGT.OsinComponents.val_mem_fam_of_isCompOf D (hlet _ (List.getElem_mem hi))
      hlam
  refine hex (i + 1) (by omega) (by omega) ?_
  rw [hspan]
  exact hval

end SideGap

end HullSC
end GroupApproximation
