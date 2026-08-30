import GroupApproximation.GGT.OsinTheorem54SepPolygon
import GroupApproximation.GGT.OsinTheorem54SepComponents

/-!
# Every component of a geodesic word is one letter

A geodesic word cannot carry two adjacent letters of the same index: the family
is a subgroup, so their product is a single `H_λ`-letter and spells the same
element in one letter fewer, contradicting minimality --- and if the product is
trivial, dropping both is shorter still.  So a maximal `H_λ`-run of a geodesic
word has length one.

## The proof, and why it is four lines rather than an import

The span of a component lies in `H_λ` (`span_mem_fam_of_isComp`), so the two
endpoints of the run are ONE letter apart in `Γ(G, X ⊔ ℋ)`; and geodesy says
they are at least `k - i` apart (`sub_le_wordDist_vertex`).  Hence `k - i ≤ 1`,
and `i < k` finishes it.

`DGOIsolatedComponentBridge.isComp_eq_succ_of_geodesic` proves the same fact for
fp-geometry over the `(1,0)` clause directly, and this module used to be a
one-line wrapper around it.  It is written out instead so that the dependency
runs the right way: this is a low module in the §5 chain, and importing the
`DGO` isolated-component tower from it put a high module underneath a low one
for a fact that costs four lines.  The import graph is the whole reason ---
`GGT/OsinTheorem54SepSplice.lean` and the `qp₂`-inheritance of Lemma 5.6 sit on
top of this file, and a build cycle through it is exactly what a swept import
line produced once already.

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
    {i k : ℕ} (hcomp : IsComp lam ws i k) : k = i + 1 := by
  have hspan : (vertex f ws i)⁻¹ * vertex f ws k ∈ D.fam lam :=
    span_mem_fam_of_isComp D f hw.1 hcomp
  have hone : wordDist D.alphabet.carrier (vertex f ws i) (vertex f ws k) ≤ 1 := by
    show wordNorm D.alphabet.carrier ((vertex f ws i)⁻¹ * vertex f ws k) ≤ 1
    exact wordNorm_le_one_of_mem (Or.inr (Set.mem_iUnion.mpr ⟨lam, hspan⟩))
  have hsub := sub_le_wordDist_vertex D hw i k (le_of_lt hcomp.1) hcomp.2.1
  have hik := hcomp.1
  omega

end OsinComponents
end GGT
end GroupApproximation
