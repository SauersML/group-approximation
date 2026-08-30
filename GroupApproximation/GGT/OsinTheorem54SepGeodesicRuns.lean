import GroupApproximation.GGT.DGOIsolatedComponentBridge

/-!
# Every component of a geodesic word is one letter

A geodesic word cannot carry two adjacent letters of the same index: the family
is a subgroup, so their product is a single `H_λ`-letter and spells the same
element in one letter fewer, contradicting minimality --- and if the product is
trivial, dropping both is shorter still.  So a maximal `H_λ`-run of a geodesic
word has length one.

`DGOIsolatedComponentBridge.isComp_eq_succ_of_geodesic` is that fact in the form
fp-geometry needed it, over the `(1,0)` clause `k - i ≤ d(vertexᵢ, vertexₖ)`.
This module supplies it over `IsGeodesicWord`, which is the form the §5 chain
and the `qp₂`-inheritance of Lemma 5.6 consume: there the clause comes from
`sub_le_wordDist_vertex`, so nothing is assumed beyond the word being geodesic.

## What it settles

The seam that would break inheritance under this development's definition of
essential penetration cannot occur.  A run of `q` continuing into the initial
letter of `p₂` inside the geodesic `q · p₂` would be two adjacent same-index
letters of a geodesic word; there are none, so no run ever extends across the
splice, and a component of `q` is a component of `q · p₂` with the SAME span ---
which is what makes the inheritance hold with essentiality carried identically
rather than re-measured.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A component of a geodesic word is a single letter.** -/
theorem isComp_eq_succ_of_isGeodesicWord (D : RelGenSet G Λ) (lam : Λ)
    {f g : G} {ws : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g ws)
    {i k : ℕ} (hcomp : IsComp lam ws i k) : k = i + 1 :=
  isComp_eq_succ_of_geodesic D lam f hw.1 hcomp
    (sub_le_wordDist_vertex D hw i k (le_of_lt hcomp.1) hcomp.2.1)

end OsinComponents
end GGT
end GroupApproximation
