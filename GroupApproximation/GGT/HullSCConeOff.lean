import GroupApproximation.Manuscript.NonMF.HullBallForm

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
has to be built.  That model is `conedAlphabet` below, and it is the alphabet
in which the phrase

> `{Hλ} ↪_h (G, X)`, i.e. `Γ(G, X ⊔ ⊔ Hλ)` is hyperbolic and each `Hλ`
> carries a locally finite relative metric

of Osin's definition of a hyperbolically embedded subgroup is stated.  So the
combinatorial cone-off is not an approximation to the object Hull uses: it is
the object, and `Alphabet`/`Cayley` of
`Manuscript.NonMF.AcylindricallyHyperbolic` already carries it.

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
* `conedAlphabet` -- the cone-off alphabet `A ∪ H`, with its symmetry and
  generation proved, so that `Cayley (conedAlphabet A H)` is the coned-off
  Cayley graph as a pseudometric space with a `G`-action by isometries.
* `wordNorm_conedAlphabet_le`, `coneOff_dist_le` -- the cone-off does not
  increase distances, and each coset of `H` has diameter at most one in it.
  The second is the defining property of a cone: the coset is crushed.
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

/-- **The cone-off of `Γ(G,A)` along the cosets of `H`**, as an alphabet:
every element of `H` is adjoined as a letter.

This is Osin's `X ⊔ H`, the alphabet in which `Γ(G, X ⊔ H)` -- the space whose
hyperbolicity is the first clause of `H ↪_h (G,X)` -- is written.  For a family
`{Hλ}` the same definition with `⋃ λ, Hλ` in place of `H` is the coned-off
graph of DGO; Hull's Theorem 7.1 uses a single hyperbolically embedded
virtually cyclic subgroup, so the single-subgroup form is the one carried
here. -/
def conedAlphabet {G : Type u} [Group G] (A : Alphabet G) (H : Subgroup G) :
    Alphabet G where
  carrier := A.carrier ∪ (H : Set G)
  symmetricGenerating := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact Or.inl (A.symmetricGenerating.inv_mem x hx)
      · exact Or.inr (H.inv_mem hx)
    · refine eq_top_iff.mpr ?_
      rw [← A.symmetricGenerating.closure_eq]
      exact Subgroup.closure_mono Set.subset_union_left

@[simp] theorem conedAlphabet_carrier {G : Type u} [Group G] (A : Alphabet G)
    (H : Subgroup G) :
    (conedAlphabet A H).carrier = A.carrier ∪ (H : Set G) := rfl

/-- The letters of `A` are letters of the cone-off. -/
theorem subset_conedAlphabet {G : Type u} [Group G] (A : Alphabet G)
    (H : Subgroup G) : A.carrier ⊆ (conedAlphabet A H).carrier :=
  Set.subset_union_left

/-- **Coning off does not increase distances.**  Every `A`-word is a word in
the larger alphabet. -/
theorem wordNorm_conedAlphabet_le {G : Type u} [Group G] (A : Alphabet G)
    (H : Subgroup G) (g : G) :
    wordNorm (conedAlphabet A H).carrier g ≤ wordNorm A.carrier g :=
  wordNorm_mono (subset_conedAlphabet A H)
    (wordLengths_nonempty A.symmetricGenerating g)

/-- **The cone crushes the coset.**  Two points of the same coset of `H` are at
distance at most one in the cone-off, whatever their distance in `Γ(G,A)`.
This is the property that the hyperbolic cone of DGO is built to have, and it
is a one-line consequence of the combinatorial model. -/
theorem coneOff_dist_le {G : Type u} [Group G] (A : Alphabet G) (H : Subgroup G)
    (g : G) {h : G} (hh : h ∈ H) :
    wordDist (conedAlphabet A H).carrier g (g * h) ≤ 1 := by
  have hstep : wordDist (conedAlphabet A H).carrier (g * 1) (g * h)
      = wordDist (conedAlphabet A H).carrier 1 h :=
    wordDist_left_invariant _ g 1 h
  rw [mul_one] at hstep
  rw [hstep, wordDist_one_left]
  exact wordNorm_le_one_of_mem (Or.inr hh)

/-- Each element of `H` is a letter of the cone-off, so lies in its unit
ball. -/
theorem mem_cayleyBall_one_conedAlphabet {G : Type u} [Group G] (A : Alphabet G)
    (H : Subgroup G) {h : G} (hh : h ∈ H) :
    h ∈ cayleyBall (conedAlphabet A H) 1 := by
  rw [mem_cayleyBall_iff, wordDist_one_left]
  exact wordNorm_le_one_of_mem (Or.inr hh)

end HullSC
end GroupApproximation
