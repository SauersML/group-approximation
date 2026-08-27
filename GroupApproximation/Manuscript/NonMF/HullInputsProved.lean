import GroupApproximation.Manuscript.NonMF.HullSmallCancellation

/-!
# The Hull citations, and the one that torsion-freeness discharges

`HullInputs` bundles four results the section *"A torsion-free group with full
MF radical"* cites: Hull's Theorem 7.1, the remark on the kernel of his
quotient map, Osin's Lemma 7.1, and Hull's Corollary 5.7 with Lemma 5.8.  Three
of them are geometry this repository does not have.  The fourth is not:
`HullInputs.twoGeneratedSuitable` splits into a clause that follows from the
definition of non-elementarity and a clause that is free over a torsion-free
ambient group, and `lem:saturation` — the only consumer — applies it at a
torsion-free group.

## The two clauses of Hull's Corollary 5.7 with Lemma 5.8

Suitability is `ActsNonElementarily N Γ` together with
`HullSuitable.NormalizesNoNontrivialFinite N`.

* Non-elementarity is *contains two independent loxodromic elements*
  (`HullGeometry.ActsNonElementarily`), so the two elements it hands out
  already generate a non-elementary subgroup: they lie in the subgroup they
  generate, and loxodromy and independence are conditions on the elements and
  not on the subgroup.  That is `exists_pair_actsNonElementarily`, and no
  geometry enters it.
* Hull's Definition 1.4(3) is free over a torsion-free ambient group, since
  there is no nontrivial finite subgroup for anything to normalize
  (`HullSuitable.normalizesNoNontrivialFinite_of_torsionFree`).

Together they are `exists_pair_suitable_of_torsionFree`: **over a torsion-free
group, Hull's Corollary 5.7 with Lemma 5.8 is a theorem of this repository.**
What Hull's argument is needed for is the general case, where the two
loxodromics his ping-pong produces are chosen so that the subgroup they
generate normalizes no nontrivial finite subgroup; that choice is what the
hyperbolic embedding of `⟨h⟩` in his Lemma 5.8 buys, and it is exactly what
torsion-freeness makes unnecessary.

`HullInputs.twoGeneratedSuitable` is nonetheless stated for an arbitrary
ambient group, so the field as recorded is not this theorem.  Adding
`IsPowerTorsionFree G` to it would make it one: `Saturation.saturation` has
`hG : IsPowerTorsionFree G` in scope at the point of application, and passes it
to `suitable_of_torsionFree` one line earlier.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFree

open GroupApproximation.HullGeometry

universe u

/-- **The non-elementarity clause of Hull's Corollary 5.7 with Lemma 5.8, with
no geometry.**  A subgroup acting non-elementarily contains two independent
loxodromic elements, and those two elements generate a subgroup that acts
non-elementarily for the same reason: the witnesses are unchanged. -/
theorem exists_pair_actsNonElementarily {G : Type u} [Group G] {A : Alphabet G}
    {N : Subgroup G} (hN : ActsNonElementarily N (Cayley.base A)) :
    ∃ h₁ ∈ N, ∃ h₂ ∈ N,
      ActsNonElementarily (Subgroup.closure ({h₁, h₂} : Set G))
        (Cayley.base A) := by
  obtain ⟨g₁, hg₁, g₂, hg₂, hlox₁, hlox₂, hind⟩ := hN
  refine ⟨g₁, hg₁, g₂, hg₂, g₁, ?_, g₂, ?_, hlox₁, hlox₂, hind⟩
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

/-- **Hull's Corollary 5.7 with Lemma 5.8, over a torsion-free ambient group.**

> `N` contains two elements `h₁, h₂` such that `N₀ = ⟨h₁, h₂⟩` is again
> suitable.

The first clause of Hull's Definition 1.4 is `exists_pair_actsNonElementarily`
and the third is `HullSuitable.normalizesNoNontrivialFinite_of_torsionFree`, so
over a torsion-free group the statement `HullInputs.twoGeneratedSuitable`
records as a citation is proved here.  The general case, where the ambient
group has torsion, is Hull's and stays a citation. -/
theorem exists_pair_suitable_of_torsionFree {G : Type u} [Group G]
    (hG : IsPowerTorsionFree G) {A : Alphabet G} {N : Subgroup G}
    (hN : Suitable A N) :
    ∃ h₁ ∈ N, ∃ h₂ ∈ N, Suitable A (Subgroup.closure ({h₁, h₂} : Set G)) := by
  obtain ⟨h₁, hh₁, h₂, hh₂, hne⟩ :=
    exists_pair_actsNonElementarily hN.actsNonElementarily
  exact ⟨h₁, hh₁, h₂, hh₂, hne,
    HullSuitable.normalizesNoNontrivialFinite_of_torsionFree hG _⟩

end TorsionFree
end NonMF
end Manuscript
end GroupApproximation
