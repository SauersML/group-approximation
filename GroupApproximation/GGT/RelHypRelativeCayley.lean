import GroupApproximation.Manuscript.NonMF.AcylindricallyHyperbolic

/-!
# The relative Cayley graph `Γ(G, X ⊔ ℋ)`

D. Osin, *Relatively hyperbolic groups: intrinsic geometry, algebraic
properties, and algorithmic problems*, Mem. Amer. Math. Soc. 179 (2006), §2,
and *Small cancellations over relatively hyperbolic groups and embedding
theorems*, Ann. of Math. 172 (2010) 1--39, §2.  This module supplies the
substrate of both: the alphabet `X ⊔ ℋ`, its word metric, and the graph
`Γ(G, X ⊔ ℋ)` as a pseudometric space.

## The two generating sets, and why they are not the same object

A relatively hyperbolic pair is a group `G` together with a family
`{H_λ}_{λ ∈ Λ}` of *peripheral* subgroups.  Osin's standing hypothesis is that
`G` is **finitely generated relative to** the family: there is a finite set
`X ⊆ G` with

    ⟨X ∪ ⋃_λ H_λ⟩ = G,

and this is strictly weaker than asking `X` to generate `G`.  In the case the
Fournier-Facio argument uses, `G = U ∗ H` with peripheral family `{U}`, the set
`X` is a finite generating set of `H` and generates nothing like `G` on its
own: every element of `U` is reached only by using peripheral letters.

That is why `RelativeGeneratingSet` below is a structure of its own rather than
an `Alphabet`.  `Manuscript.NonMF.TorsionFree.Alphabet` requires its carrier to
generate `G`, which the relative generating set does not; what does generate
`G` is the union `X ∪ ⋃_λ H_λ`, and `RelativeGeneratingSet.alphabet` is exactly
that union, packaged as an `Alphabet` so that the whole `Cayley` apparatus --
the pseudometric, the isometric translation action, the balls -- applies to it
unchanged.

## What is proved here

Everything below is proved; nothing is postulated.

* `RelativeGeneratingSet.alphabet` -- the union is symmetric and generating, so
  `Γ(G, X ⊔ ℋ)` is a pseudometric space with a `G`-action by isometries, with
  no new metric theory.
* `relLength`, `relDist` -- the relative word length and metric, and the four
  metric laws, inherited from `Algebra/WordMetric.lean`.
* `relLength_le_one_of_mem_peripheral`, `relDist_le_one_of_mem_peripheral` --
  **the peripheral cosets are crushed**: every element of every `H_λ` is a
  single letter, so a coset `gH_λ` has diameter at most one.  This is the
  defining property of the combinatorial cone-off, and it is what makes the
  relative metric a genuinely different object from the word metric of `X`.
* `avoiding`, `avoiding_subset_alphabet` -- the alphabet of paths that avoid
  one peripheral subgroup.  This is the alphabet in which the second clause of
  Osin's (equivalently Dahmani--Guirardel--Osin's) definition -- that the
  induced metric on each `H_λ` is locally finite -- is stated, and
  `GGT/RelHypDefinition.lean` states it there.

The single-subgroup case of `alphabet` is `HullSC.conedAlphabet` of
`GGT/HullSCConeOff.lean`, written for Hull's hyperbolically embedded virtually
cyclic subgroup; that module is not imported here, so that this one depends
only on modules already in the root import closure.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-- **Osin's relative generating set.**  A finite symmetric `X ⊆ G` which,
*together with* the peripheral subgroups, generates `G`.

The finiteness field is Osin's standing hypothesis and is what makes the
relative Dehn function and the small-cancellation parameters meaningful; the
symmetry field is what makes the relative word metric symmetric. -/
structure RelativeGeneratingSet (G : Type u) [Group G] {ι : Type v}
    (H : ι → Subgroup G) where
  /-- The non-peripheral letters `X`. -/
  carrier : Set G
  /-- `X` is finite. -/
  finite : carrier.Finite
  /-- `X` is closed under inversion. -/
  inv_mem : ∀ x ∈ carrier, x⁻¹ ∈ carrier
  /-- `X` generates `G` **relative to** the peripheral family: it is the union
  with the peripheral subgroups that generates, not `X` itself. -/
  closure_eq : Subgroup.closure (carrier ∪ ⋃ l, (H l : Set G)) = ⊤

namespace RelativeGeneratingSet

variable {G : Type u} [Group G] {ι : Type v} {H : ι → Subgroup G}

/-- **The relative alphabet `X ⊔ ℋ`**, as an `Alphabet` of `G`: the letters are
`X` together with every element of every peripheral subgroup.

Symmetry is inherited from `X` on the left and from the subgroup axioms on the
right; generation is the relative generation hypothesis, verbatim. -/
def alphabet (X : RelativeGeneratingSet G H) : Alphabet G where
  carrier := X.carrier ∪ ⋃ l, (H l : Set G)
  symmetricGenerating := by
    refine ⟨?_, X.closure_eq⟩
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (X.inv_mem x hx)
    · rw [Set.mem_iUnion] at hx
      obtain ⟨l, hl⟩ := hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨l, (H l).inv_mem hl⟩)

theorem alphabet_carrier (X : RelativeGeneratingSet G H) :
    X.alphabet.carrier = X.carrier ∪ ⋃ l, (H l : Set G) := rfl

/-- Every non-peripheral letter is a letter of the relative alphabet. -/
theorem subset_alphabet (X : RelativeGeneratingSet G H) :
    X.carrier ⊆ X.alphabet.carrier := by
  rw [X.alphabet_carrier]
  exact Set.subset_union_left

/-- Every element of every peripheral subgroup is a letter of the relative
alphabet.  This is the whole difference between `Γ(G, X)` and
`Γ(G, X ⊔ ℋ)`. -/
theorem peripheral_subset_alphabet (X : RelativeGeneratingSet G H) (l : ι) :
    (H l : Set G) ⊆ X.alphabet.carrier := by
  rw [X.alphabet_carrier]
  intro x hx
  exact Or.inr (Set.mem_iUnion.mpr ⟨l, hx⟩)

/-- **The relative word length** `|g|_{X ⊔ ℋ}`. -/
noncomputable def relLength (X : RelativeGeneratingSet G H) (g : G) : ℕ :=
  wordNorm X.alphabet.carrier g

/-- **The relative word metric**, which is the vertex metric of
`Γ(G, X ⊔ ℋ)`. -/
noncomputable def relDist (X : RelativeGeneratingSet G H) (g h : G) : ℕ :=
  wordDist X.alphabet.carrier g h

theorem relDist_eq (X : RelativeGeneratingSet G H) (g h : G) :
    X.relDist g h = X.relLength (g⁻¹ * h) := rfl

/-- A non-peripheral letter has relative length at most one. -/
theorem relLength_le_one_of_mem_carrier (X : RelativeGeneratingSet G H) {g : G}
    (hg : g ∈ X.carrier) : X.relLength g ≤ 1 :=
  wordNorm_le_one_of_mem (X.subset_alphabet hg)

/-- **A peripheral element is a single letter**, however long its `X`-word
would be.  This asymmetry between the peripheral subgroups and the rest of the
group is the entire content of the relative metric. -/
theorem relLength_le_one_of_mem_peripheral (X : RelativeGeneratingSet G H)
    (l : ι) {g : G} (hg : g ∈ H l) : X.relLength g ≤ 1 :=
  wordNorm_le_one_of_mem (X.peripheral_subset_alphabet l hg)

theorem relLength_one (X : RelativeGeneratingSet G H) : X.relLength 1 = 0 :=
  wordNorm_one X.alphabet.carrier

theorem relLength_eq_zero_iff (X : RelativeGeneratingSet G H) (g : G) :
    X.relLength g = 0 ↔ g = 1 :=
  wordNorm_eq_zero_iff X.alphabet.symmetricGenerating g

theorem relLength_mul_le (X : RelativeGeneratingSet G H) (g h : G) :
    X.relLength (g * h) ≤ X.relLength g + X.relLength h :=
  wordNorm_mul_le X.alphabet.symmetricGenerating g h

theorem relLength_inv (X : RelativeGeneratingSet G H) (g : G) :
    X.relLength g⁻¹ = X.relLength g :=
  wordNorm_inv X.alphabet.symmetricGenerating g

theorem relDist_self (X : RelativeGeneratingSet G H) (g : G) :
    X.relDist g g = 0 :=
  wordDist_self X.alphabet.carrier g

theorem relDist_comm (X : RelativeGeneratingSet G H) (g h : G) :
    X.relDist g h = X.relDist h g :=
  wordDist_comm X.alphabet.symmetricGenerating g h

theorem relDist_triangle (X : RelativeGeneratingSet G H) (g h k : G) :
    X.relDist g k ≤ X.relDist g h + X.relDist h k :=
  wordDist_triangle X.alphabet.symmetricGenerating g h k

theorem relDist_eq_zero_iff (X : RelativeGeneratingSet G H) (g h : G) :
    X.relDist g h = 0 ↔ g = h :=
  wordDist_eq_zero_iff X.alphabet.symmetricGenerating g h

theorem relDist_left_invariant (X : RelativeGeneratingSet G H) (g x y : G) :
    X.relDist (g * x) (g * y) = X.relDist x y :=
  wordDist_left_invariant X.alphabet.carrier g x y

theorem relDist_one_left (X : RelativeGeneratingSet G H) (g : G) :
    X.relDist 1 g = X.relLength g :=
  wordDist_one_left X.alphabet.carrier g

/-- **The cone crushes the coset.**  Two points of the same peripheral coset
are at relative distance at most one, whatever their distance in `Γ(G, X)`. -/
theorem relDist_le_one_of_mem_peripheral (X : RelativeGeneratingSet G H)
    (l : ι) (g : G) {h : G} (hh : h ∈ H l) : X.relDist g (g * h) ≤ 1 := by
  have hstep : X.relDist (g * 1) (g * h) = X.relDist 1 h :=
    X.relDist_left_invariant g 1 h
  rw [mul_one] at hstep
  rw [hstep, X.relDist_one_left]
  exact X.relLength_le_one_of_mem_peripheral l hh

/-- **Enlarging the alphabet does not increase length.**  Any alphabet
contained in `X ⊔ ℋ` in which `g` is spellable gives an upper bound for the
relative length of `g`. -/
theorem relLength_le_wordNorm (X : RelativeGeneratingSet G H) {S : Set G}
    (hS : S ⊆ X.alphabet.carrier) {g : G} (hg : (wordLengths S g).Nonempty) :
    X.relLength g ≤ wordNorm S g :=
  wordNorm_mono hS hg

/-- **The relative Cayley graph `Γ(G, X ⊔ ℋ)`**, as a pseudometric space with
an isometric `G`-action.  Nothing new is built: it is the `Cayley` construction
of `Manuscript.NonMF.AcylindricallyHyperbolic` at the relative alphabet. -/
abbrev relativeCayley (X : RelativeGeneratingSet G H) : Type u :=
  Cayley X.alphabet

theorem relativeCayley_dist (X : RelativeGeneratingSet G H)
    (x y : Cayley X.alphabet) :
    dist x y = (X.relDist (Cayley.val x) (Cayley.val y) : ℝ) :=
  Cayley.dist_eq x y

/-- **The letters available to a path avoiding the `l`-th peripheral
subgroup**: everything except the letters of `H l` itself.

Dahmani--Guirardel--Osin's second clause, and Osin's local finiteness of the
induced metric on a peripheral subgroup, are statements about the word metric
of this alphabet restricted to `H l`. -/
def avoiding (X : RelativeGeneratingSet G H) (l : ι) : Set G :=
  X.carrier ∪ ⋃ (m : ι) (_ : m ≠ l), (H m : Set G)

theorem avoiding_subset_alphabet (X : RelativeGeneratingSet G H) (l : ι) :
    X.avoiding l ⊆ X.alphabet.carrier := by
  intro g hg
  rcases hg with hg | hg
  · exact X.subset_alphabet hg
  · rw [Set.mem_iUnion] at hg
    obtain ⟨m, hm⟩ := hg
    rw [Set.mem_iUnion] at hm
    obtain ⟨-, hm⟩ := hm
    exact X.peripheral_subset_alphabet m hm

/-- The avoiding alphabet is symmetric, as the relative alphabet is; it is
*not* claimed to generate, and in general it does not. -/
theorem avoiding_inv_mem (X : RelativeGeneratingSet G H) (l : ι) {g : G}
    (hg : g ∈ X.avoiding l) : g⁻¹ ∈ X.avoiding l := by
  rcases hg with hg | hg
  · exact Or.inl (X.inv_mem g hg)
  · rw [Set.mem_iUnion] at hg
    obtain ⟨m, hm⟩ := hg
    rw [Set.mem_iUnion] at hm
    obtain ⟨hml, hm⟩ := hm
    exact Or.inr (Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hml, (H m).inv_mem hm⟩⟩)

end RelativeGeneratingSet

end RelHyp
end GGT
end GroupApproximation
