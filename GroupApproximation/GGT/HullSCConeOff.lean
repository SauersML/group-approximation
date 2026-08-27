import GroupApproximation.Manuscript.NonMF.HullBallForm
import GroupApproximation.GGT.WPDHyperbolicallyEmbedded

/-!
# The cone-off of a Cayley graph, and word length along a homomorphism

This is the geometric substrate of Hull's small cancellation theory
(M. Hull, *Small cancellation in acylindrically hyperbolic groups*,
Groups Geom. Dyn. 10 (2016) 1077-1119) and of the rotating-family machinery of
Dahmani-Guirardel-Osin (*Hyperbolically embedded subgroups and rotating
families in groups acting on hyperbolic spaces*, Mem. Amer. Math. Soc. 245
(2017), no. 1156).

## What a cone-off is, and which one is formalized here

DGO cone off a hyperbolic space `X` along a family of quasi-convex subsets by
gluing a hyperbolic cone of radius `r` onto each subset.  In the group case --
the only case Hull's Theorem 7.1 uses -- the space is a Cayley graph
`Γ(G, A)` and the subsets are the cosets of a subgroup `H`, and there the
cone-off has a purely combinatorial model: it is the Cayley graph of `G` with
respect to the enlarged alphabet `A ∪ H`.  Adding every element of `H` as a
letter collapses each coset `gH` to a set of diameter one, which is exactly
what the cone of radius one does, and no metric on a quotient of `Y × [0,r]`
has to be built.  That alphabet is the one in which the phrase

> `{Hλ} ↪_h (G, X)`, i.e. `Γ(G, X ⊔ ⊔ Hλ)` is hyperbolic and each `Hλ`
> carries a locally finite relative metric

of Osin's definition of a hyperbolically embedded subgroup is stated, so it is
already in the repository: it is `GGT.RelGenSet.alphabet` of
`GGT/WPDHyperbolicallyEmbedded.lean`, and this module does not restate it.
`HullSC.coneOff` is that relative generating set for the one-element family
`{H}`.  The combinatorial cone-off is not an approximation to the object Hull
uses: it is the object.

## What is proved here

Everything in this module is proved; nothing is postulated.

* `wordNorm_map_le`, `wordDist_map_le` -- **word length does not increase along
  a homomorphism carrying letters to letters.**  Spelling `g` in `A` and
  applying `φ` letter by letter spells `φ g` in `B`.
* `mem_cayleyBall_iff`, `image_cayleyBall_subset` -- consequently a
  homomorphism carrying `A` into `B` carries the `R`-ball of `Γ(G,A)` into the
  `R`-ball of `Γ(Q,B)`.  This is the lemma that makes an induction along a
  tower of quotients possible at all: without it the injectivity radius of the
  composite of two Hull quotients cannot be controlled, because the balls of
  `Γ(G,A)` are infinite when `A` is (and Hull's `A` is infinite in general).
* `coneOff`, `coneOff_carrier` -- the cone-off as a `GGT.RelGenSet`, with its
  symmetry and generation proved, so that `Cayley (coneOff A H).alphabet` is
  the coned-off Cayley graph as a pseudometric space with a `G`-action by
  isometries.
* `wordNorm_coneOff_le`, `coneOff_dist_le` -- the cone-off does not increase
  distances, and each coset of `H` has diameter at most one in it.  The second
  is the defining property of a cone: the coset is crushed.
* `isHypEmbeddedOf_coneOff` -- **the cone-off is the witness for `H ↪_h (G,A)`**.
  So what has to be established about `E(g)` in Hull's Theorem 5.1 is a
  statement about `Cayley (coneOff A E(g)).alphabet` and about that relative
  generating set's `relBall`, and nothing else.

One inherited convention, documented in `GGT/WPDHyperbolicallyEmbedded.lean` and
recorded here because `coneOff` inherits it: the hyperbolicity clause is stated
against the word metric of the *set* `X ∪ ⋃ Hλ` rather than of the disjoint
union, since duplicating a letter creates parallel edges and does not change
the vertex metric; the disjointness is used where it matters, in the definition
of the relative metric `d̂λ`, whose balls about `1` are `relBall`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## Word length along a homomorphism -/

/-- **Spelling travels along a homomorphism.**  If `φ` carries every letter of
`S` to a letter of `T`, then a shortest `S`-word for `g`, mapped letter by
letter, is a `T`-word for `φ g` of the same length. -/
theorem wordNorm_map_le {G : Type u} {Q : Type v} [Group G] [Group Q]
    {S : Set G} {T : Set Q} (hS : IsSymmetricGeneratingSet S) (φ : G →* Q)
    (hST : ∀ a ∈ S, φ a ∈ T) (g : G) :
    wordNorm T (φ g) ≤ wordNorm S g := by
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hS g
  have hword : IsWord T (l.map φ) (φ g) := by
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hST y (hl.letters y hy)
    · rw [← map_list_prod φ l, hl.prod_eq]
  have hle := wordNorm_le_length hword
  rw [List.length_map, hlen] at hle
  exact hle

/-- The word metric does not increase along a homomorphism carrying letters to
letters. -/
theorem wordDist_map_le {G : Type u} {Q : Type v} [Group G] [Group Q]
    {S : Set G} {T : Set Q} (hS : IsSymmetricGeneratingSet S) (φ : G →* Q)
    (hST : ∀ a ∈ S, φ a ∈ T) (x y : G) :
    wordDist T (φ x) (φ y) ≤ wordDist S x y := by
  have hmap : (φ x)⁻¹ * φ y = φ (x⁻¹ * y) := by
    rw [map_mul, map_inv]
  unfold wordDist
  rw [hmap]
  exact wordNorm_map_le hS φ hST (x⁻¹ * y)

/-! ## Balls of the Cayley graph -/

/-- Membership in the ball of `Γ(G,A)` about the basepoint is a statement about
the word length, with no real numbers in it. -/
theorem mem_cayleyBall_iff {G : Type u} [Group G] (A : Alphabet G) (R : ℕ)
    (x : G) : x ∈ cayleyBall A R ↔ wordDist A.carrier 1 x ≤ R := by
  constructor
  · intro hx
    have hx' : ((wordDist A.carrier 1 x : ℕ) : ℝ) ≤ (R : ℝ) := hx
    exact_mod_cast hx'
  · intro hx
    show ((wordDist A.carrier 1 x : ℕ) : ℝ) ≤ (R : ℝ)
    exact_mod_cast hx

/-- **Balls map into balls.**  A homomorphism carrying the alphabet of `G` into
the alphabet of `Q` carries the `R`-ball of `Γ(G,A)` into the `R`-ball of
`Γ(Q,B)`, at the same radius.

This is what lets the injectivity radius of a composite of quotient maps be
controlled by the injectivity radii of the factors: see
`HullSC.injOn_comp_of_image_subset`. -/
theorem image_cayleyBall_subset {G : Type u} {Q : Type v} [Group G] [Group Q]
    (A : Alphabet G) (B : Alphabet Q) (φ : G →* Q)
    (hAB : ∀ a ∈ A.carrier, φ a ∈ B.carrier) (R : ℕ) :
    (φ : G → Q) '' cayleyBall A R ⊆ cayleyBall B R := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_cayleyBall_iff] at hx ⊢
  have hstep := wordDist_map_le A.symmetricGenerating φ hAB 1 x
  rw [map_one] at hstep
  exact le_trans hstep hx

/-- The composite of two maps, each injective on the relevant ball, is
injective on the first ball.  The middle step is `image_cayleyBall_subset`. -/
theorem injOn_comp_of_image_subset {G : Type u} {Q : Type v} {P : Type*}
    [Group G] [Group Q] [Group P] (A : Alphabet G) (B : Alphabet Q)
    (φ : G →* Q) (ψ : Q →* P) (hAB : ∀ a ∈ A.carrier, φ a ∈ B.carrier)
    (R : ℕ) (hφ : Set.InjOn φ (cayleyBall A R))
    (hψ : Set.InjOn ψ (cayleyBall B R)) :
    Set.InjOn (ψ.comp φ) (cayleyBall A R) := by
  intro x hx y hy hxy
  have hxB : φ x ∈ cayleyBall B R :=
    image_cayleyBall_subset A B φ hAB R ⟨x, hx, rfl⟩
  have hyB : φ y ∈ cayleyBall B R :=
    image_cayleyBall_subset A B φ hAB R ⟨y, hy, rfl⟩
  have hmid : φ x = φ y := hψ hxB hyB hxy
  exact hφ hx hy hmid

/-! ## The cone-off alphabet -/

/-- **The cone-off of `Γ(G,A)` along the cosets of `H`**, as a relative
generating set in the sense of `GGT.RelGenSet`: base `A`, and the one-element
family `{H}`.

The alphabet it carries, `GGT.RelGenSet.alphabet`, is Osin's `X ⊔ H` -- the
alphabet in which `Γ(G, X ⊔ H)`, the space whose hyperbolicity is the first
clause of `H ↪_h (G,X)`, is written.  The definition of the relative generating
set and of `↪_h` belongs to the `GGT.WPDHyperbolicallyEmbedded` lane and is
used here rather than restated; what this module adds is the reading of that
alphabet as a *cone-off*, which is what DGO's rotating families act on. -/
def coneOff {G : Type u} [Group G] (A : Alphabet G) (H : Subgroup G) :
    GGT.RelGenSet G Unit where
  base := A.carrier
  fam := fun _ => H
  symmetricGenerating := by
    show IsSymmetricGeneratingSet (A.carrier ∪ ⋃ _ : Unit, (H : Set G))
    have hconst : (⋃ _ : Unit, (H : Set G)) = (H : Set G) := by
      ext x
      simp
    rw [hconst]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact Or.inl (A.symmetricGenerating.inv_mem x hx)
      · exact Or.inr (H.inv_mem hx)
    · refine eq_top_iff.mpr ?_
      rw [← A.symmetricGenerating.closure_eq]
      exact Subgroup.closure_mono Set.subset_union_left

/-- The letters of the cone-off are the letters of `A` together with the
elements of `H`. -/
theorem coneOff_carrier {G : Type u} [Group G] (A : Alphabet G)
    (H : Subgroup G) :
    (coneOff A H).alphabet.carrier = A.carrier ∪ (H : Set G) := by
  have hconst : (⋃ _ : Unit, (H : Set G)) = (H : Set G) := by
    ext x
    simp
  show A.carrier ∪ (⋃ _ : Unit, (H : Set G)) = A.carrier ∪ (H : Set G)
  rw [hconst]

/-- The letters of `A` are letters of the cone-off. -/
theorem subset_coneOff {G : Type u} [Group G] (A : Alphabet G)
    (H : Subgroup G) : A.carrier ⊆ (coneOff A H).alphabet.carrier := by
  rw [coneOff_carrier]
  exact Set.subset_union_left

/-- Every element of `H` is a letter of the cone-off. -/
theorem mem_coneOff_of_mem {G : Type u} [Group G] (A : Alphabet G)
    {H : Subgroup G} {h : G} (hh : h ∈ H) :
    h ∈ (coneOff A H).alphabet.carrier := by
  rw [coneOff_carrier]
  exact Or.inr hh

/-- **Coning off does not increase distances.**  Every `A`-word is a word in
the larger alphabet. -/
theorem wordNorm_coneOff_le {G : Type u} [Group G] (A : Alphabet G)
    (H : Subgroup G) (g : G) :
    wordNorm (coneOff A H).alphabet.carrier g ≤ wordNorm A.carrier g :=
  wordNorm_mono (subset_coneOff A H)
    (wordLengths_nonempty A.symmetricGenerating g)

/-- **The cone crushes the coset.**  Two points of the same coset of `H` are at
distance at most one in the cone-off, whatever their distance in `Γ(G,A)`.
This is the property that the hyperbolic cone of DGO is built to have, and in
the combinatorial model it is one line. -/
theorem coneOff_dist_le {G : Type u} [Group G] (A : Alphabet G) (H : Subgroup G)
    (g : G) {h : G} (hh : h ∈ H) :
    wordDist (coneOff A H).alphabet.carrier g (g * h) ≤ 1 := by
  have hstep : wordDist (coneOff A H).alphabet.carrier (g * 1) (g * h)
      = wordDist (coneOff A H).alphabet.carrier 1 h :=
    wordDist_left_invariant _ g 1 h
  rw [mul_one] at hstep
  rw [hstep, wordDist_one_left]
  exact wordNorm_le_one_of_mem (mem_coneOff_of_mem A hh)

/-- Each element of `H` lies in the unit ball of the cone-off. -/
theorem mem_cayleyBall_one_coneOff {G : Type u} [Group G] (A : Alphabet G)
    {H : Subgroup G} {h : G} (hh : h ∈ H) :
    h ∈ cayleyBall (coneOff A H).alphabet 1 := by
  rw [mem_cayleyBall_iff, wordDist_one_left]
  exact wordNorm_le_one_of_mem (mem_coneOff_of_mem A hh)

/-- **The cone-off is the witness for `H ↪_h (G, A)`.**  Osin's definition
asks for *some* relative generating set with base `A` and family `{H}` whose
relative Cayley graph is hyperbolic and whose relative metric is locally
finite; `coneOff A H` is that relative generating set, so hyperbolicity and
local finiteness of the cone-off *are* the hyperbolic embedding.

This is the bridge between the geometry of this module and the predicate
`GGT.IsHypEmbeddedOf` that Hull's Theorem 5.1 consumes: what has to be
established about `E(g)` is a statement about `Cayley (coneOff A E(g)).alphabet`
and about `(coneOff A E(g)).relBall`, and nothing else. -/
theorem isHypEmbeddedOf_coneOff {G : Type u} [Group G] (A : Alphabet G)
    (H : Subgroup G) (h : (coneOff A H).IsHyperbolicallyEmbedded) :
    GGT.IsHypEmbeddedOf G A.carrier H :=
  ⟨coneOff A H, rfl, rfl, h⟩

end HullSC
end GroupApproximation
