import GroupApproximation.GGT.HullSCCyclicDisjointness
import GroupApproximation.GGT.HullSCRelatorSeparation2ConeOff

/-!
# Hull's §5 for a pair, with everything but the embedding discharged

`HullSC.ExistsHypEmbeddedConeOff₂` -- Hull's Corollary 5.7 with Lemma 5.8, over
a pair -- asks for five things at once: two subgroups **inside** the suitable
`N`, whose cone-off over Hull's alphabet is hyperbolically embedded, containing
independent loxodromic elements, and meeting trivially.

**Four of the five are free**, and this module proves it.  Take the subgroups to
be the cyclic groups on the two loxodromics themselves:

* `⟨hᵢ⟩ ≤ N` because `hᵢ ∈ N`, which is `Subgroup.zpowers_le`;
* `hᵢ ∈ ⟨hᵢ⟩`;
* the loxodromy and the independence are hypotheses about the `hᵢ` and are
  carried through unchanged;
* **Hull's (W4)**, that the two subgroups meet trivially, is
  `GGT.Elementary.zpowers_disjoint_of_independent` -- a common element is
  `h₀^p = h₁^q`, and nonzero exponents contradict independence.

And the two loxodromics themselves are free: `Suitable` *is*
`ActsNonElementarily N` together with the finite-subgroup clause, and the first
conjunct hands back exactly a pair of independent loxodromics in `N`.

So the citation reduces to its one geometric clause:

> for a suitable `N` there are independent loxodromic `h₀, h₁ ∈ N` with
> `{⟨h₀⟩, ⟨h₁⟩} ↪_h (G, A)`.

That is `existsHypEmbeddedConeOff₂_of_zpowers` below, whose hypothesis is that
statement and nothing else.

## What the remaining clause costs, and why this is the right shape for it

Hull gets the embedding from `E(hᵢ)`, not from `⟨hᵢ⟩`, and then has to arrange
`E(hᵢ) ≤ N` -- his Lemma 5.8, a choice argument that needs the classification of
elementary closures.  Asking for `⟨hᵢ⟩` instead moves that cost somewhere
cheaper: over a torsion-free ambient group `E(h)` is infinite cyclic, so
`⟨h⟩ ≤ E(h)` has finite index, and what is owed is a *finite-index descent* --
that a finite-index subgroup of a hyperbolically embedded subgroup is again
hyperbolically embedded, over a base enlarged by a finite transversal, which
`GGT.DGOCorollary427` then strips because it changes the base by a finite set.
A descent lemma is checkable; a choice argument about which `h` to pick is not.

The (W4) clause is worth a second look for the same reason.  Stated at arbitrary
subgroups it is a genuine hypothesis -- with torsion, `E(h₀) ∩ E(h₁)` contains
the maximal finite normal subgroup of `G`.  Stated at the cyclic ones it is a
theorem.  So the strengthening of `ExistsHypEmbeddedConeOff₂` costs nothing at
the cyclic choice and costs a real clause at the general one.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- **The two independent loxodromics of a suitable subgroup**, which is the
first conjunct of Hull's Definition 1.4 read back. -/
theorem exists_independent_lox_of_suitable {G : Type u} [Group G]
    {A : Alphabet G} {N : Subgroup G} (hN : Suitable A N) :
    ∃ g : Bool → G, (∀ b : Bool, g b ∈ N) ∧
      (∀ b : Bool, IsLoxodromic (g b) (Cayley.base A)) ∧
        Independent (g false) (g true) (Cayley.base A) := by
  obtain ⟨a, ha, b, hb, halox, hblox, hind⟩ := hN.actsNonElementarily
  refine ⟨fun c => bif c then b else a, ?_, ?_, hind⟩
  · intro c
    cases c
    · exact ha
    · exact hb
  · intro c
    cases c
    · exact halox
    · exact hblox

/-- **Hull's §5 for a pair, from its geometric clause alone.**

The hypothesis is the embedding and nothing else; the four remaining clauses of
`ExistsHypEmbeddedConeOff₂` are discharged here.  See the module header for what
this buys and what it costs. -/
theorem existsHypEmbeddedConeOff₂_of_zpowers
    (hemb : ∀ {G : Type u} [Group G] (A : HullGeneratingSet G)
      {N : Subgroup G}, Suitable A.alphabet N →
        ∃ g : Bool → G, (∀ b : Bool, g b ∈ N) ∧
          (∀ b : Bool, IsLoxodromic (g b) (Cayley.base A.alphabet)) ∧
            Independent (g false) (g true) (Cayley.base A.alphabet) ∧
              (coneOffFamily A.alphabet
                (fun b => Subgroup.zpowers (g b))).IsHyperbolicallyEmbedded) :
    ExistsHypEmbeddedConeOff₂.{u} := by
  intro G _ A N hN
  obtain ⟨g, hgN, hglox, hind, hembK⟩ := hemb A hN
  refine ⟨fun b => Subgroup.zpowers (g b), ?_, hembK, g, ?_, hglox, hind, ?_⟩
  · intro b
    exact Subgroup.zpowers_le.mpr (hgN b)
  · intro b
    exact Subgroup.mem_zpowers (g b)
  · exact GGT.Elementary.zpowers_disjoint_of_independent
      (isIsometricAction_cayley A.alphabet) (hglox false) hind

/-- **The same, from the embedding for every pair of independent loxodromics**,
which is the shape Dahmani-Guirardel-Osin's theorem has: it holds for any finite
family of pairwise non-commensurable loxodromic elements, and independence
implies non-commensurability
(`GGT.Elementary.not_independent_of_common_zpow`).

This is the sharpest form of what Hull's §5 for a pair still owes.  The
suitable subgroup has disappeared from the hypothesis entirely --- it was only
ever there to produce the two loxodromics and to hold the two subgroups, and
`exists_independent_lox_of_suitable` produces them while `Subgroup.zpowers_le`
holds them:

> for any two independent loxodromic elements of `Γ(G,A)`, the cone-off of `A`
> along the cyclic subgroups they generate is hyperbolically embedded. -/
theorem existsHypEmbeddedConeOff₂_of_zpowers_forall
    (hemb : ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (g : Bool → G),
      (∀ b : Bool, IsLoxodromic (g b) (Cayley.base A.alphabet)) →
        Independent (g false) (g true) (Cayley.base A.alphabet) →
          (coneOffFamily A.alphabet
            (fun b => Subgroup.zpowers (g b))).IsHyperbolicallyEmbedded) :
    ExistsHypEmbeddedConeOff₂.{u} := by
  refine existsHypEmbeddedConeOff₂_of_zpowers ?_
  intro G _ A N hN
  obtain ⟨g, hgN, hglox, hind⟩ := exists_independent_lox_of_suitable hN
  exact ⟨g, hgN, hglox, hind, hemb A g hglox hind⟩

end HullSC
end GroupApproximation
