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
* `AvoidsPeripheral`, `peripheralLengths` -- relative paths that avoid the
  subgraph spanned by one peripheral subgroup, and their lengths.  This is the
  object Dahmani--Guirardel--Osin's second clause -- that the induced metric
  `d̂_λ` on each `H_λ` is locally finite -- is a statement about;
  `GGT/RelHypDefinition.lean` states the clause there.

  The definition is a condition on the *path*, not on the alphabet, and that
  distinction is the whole content of the clause.  Forbidding the letters of
  `H_λ` outright would be a different and much weaker demand, and would certify
  `ℤ² = ⟨a⟩ × ⟨b⟩` as hyperbolic relative to `⟨a⟩`, which it is not: the coned
  graph `Γ(ℤ², {b} ⊔ ⟨a⟩)` is quasi-isometric to a line, hence hyperbolic, and
  the only reason `⟨a⟩` is not hyperbolically embedded is that the three-step
  path `b, aⁿ, b⁻¹` joins `1` to `aⁿ` *through the other coset* `b⟨a⟩` for every
  `n`, so the balls of `d̂` are infinite.  A step across a different coset is
  legal; only a step both of whose endpoints lie in `H_λ` is not.

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

/-- **A relative path avoiding the `l`-th peripheral subgraph.**

The vertices of the path spelled by `w` are its partial products
`1 = p₀, p₁, …, p_k`, and an edge of the complete subgraph spanned by `H l` is a
step both of whose endpoints lie in `H l`.  So avoiding that subgraph is
exactly the condition below: no two consecutive vertices both lie in `H l`.

What is *not* forbidden is a step across a different coset `gH l`, and that is
the whole point -- see the module docstring for the `ℤ²` example, where
forbidding those too would wrongly certify a relatively hyperbolic pair. -/
def AvoidsPeripheral (H : ι → Subgroup G) (l : ι) (w : List G) : Prop :=
  ∀ i : ℕ, i + 1 ≤ w.length →
    ¬ ((w.take i).prod ∈ H l ∧ (w.take (i + 1)).prod ∈ H l)

/-- The empty path avoids everything: it has no steps. -/
theorem avoidsPeripheral_nil (H : ι → Subgroup G) (l : ι) :
    AvoidsPeripheral H l [] := by
  intro i hi
  rw [List.length_nil] at hi
  exact absurd hi (by omega)

/-- **A single non-peripheral letter is a legal path.**  Its one step goes from
`1` to a vertex outside `H l`, so it is not an edge of the peripheral
subgraph. -/
theorem avoidsPeripheral_singleton (H : ι → Subgroup G) (l : ι) {x : G}
    (hx : x ∉ H l) : AvoidsPeripheral H l [x] := by
  intro i hi
  rw [List.length_singleton] at hi
  have hi0 : i = 0 := by omega
  subst hi0
  rintro ⟨-, h2⟩
  exact hx (by simpa using h2)

/-- **A single peripheral letter is not.**  Both its endpoints lie in `H l`, so
it is precisely an edge of the subgraph being avoided.  This is what makes the
induced metric a genuinely different object from the relative metric, in which
the same element has length one. -/
theorem not_avoidsPeripheral_singleton (H : ι → Subgroup G) (l : ι) {x : G}
    (hx : x ∈ H l) : ¬ AvoidsPeripheral H l [x] := by
  intro hav
  refine hav 0 (by simp) ⟨?_, ?_⟩
  · simp
  · simpa using hx

/-- **The lengths of relative paths from `1` to `g` avoiding the `l`-th
peripheral subgraph.**  Empty when there is no such path, which is the `∞` of
Dahmani--Guirardel--Osin's `d̂_λ`. -/
def peripheralLengths (X : RelativeGeneratingSet G H) (l : ι) (g : G) : Set ℕ :=
  {n | ∃ w : List G, IsWord X.alphabet.carrier w g ∧ AvoidsPeripheral H l w ∧
    w.length = n}

theorem mem_peripheralLengths_iff (X : RelativeGeneratingSet G H) (l : ι) (g : G)
    (n : ℕ) :
    n ∈ X.peripheralLengths l g ↔
      ∃ w : List G, IsWord X.alphabet.carrier w g ∧ AvoidsPeripheral H l w ∧
        w.length = n :=
  Iff.rfl

/-- **The identity is at distance zero from itself**, so the induced metric is
not everywhere infinite. -/
theorem zero_mem_peripheralLengths (X : RelativeGeneratingSet G H) (l : ι) :
    0 ∈ X.peripheralLengths l 1 :=
  ⟨[], isWord_nil _, avoidsPeripheral_nil H l, rfl⟩

end RelativeGeneratingSet

end RelHyp
end GGT
end GroupApproximation
