import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.AlexanderWhitneyChainMap
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.SuccPred

/-!
# The combinatorics of Steenrod's cup-`i` products: `i`-cuts

Steenrod's `⌣ᵢ` is a sum over ways of splitting the vertices of a simplex into
two overlapping alternating families.  This file builds that index set and the
face map it produces, and nothing else: no cochains appear here, so the whole
file is finite combinatorics of `Finset (Fin N)` together with the one bridge
`faceOfFinset` from a vertex subset to a morphism of `SimplexCategory`.

## The picture

Fix cut points `c₀ < c₁ < ⋯ < cᵢ` among the vertices `0,…,m`.  They split the
vertex set into alternating blocks, which are handed out to the two factors:

```text
U = [0,c₀] ∪ [c₁,c₂] ∪ [c₃,c₄] ∪ ⋯
V =         [c₀,c₁] ∪ [c₂,c₃] ∪ ⋯
```

`U` and `V` cover everything and meet exactly in the `i+1` cut points, so

```text
|U| + |V| = (m+1) + (i+1).
```

`cutU_union_cutV` and `cutU_inter_cutV` are those two sentences, and
`cutU_card_add_cutV_card` is their consequence.

## Why the membership test is a parity

Writing `cutRank S x` for the number of cut points strictly below `x`, a vertex
lies in `U` exactly when that count is even, and in `V` exactly when it is odd
-- *except* that the cut points themselves lie in both, which is what makes the
two families overlap.  So both tests are "`x` is a cut point, or the parity is
right", which is why `cutU_inter_cutV` collapses to `S` on the nose: the parity
clauses are complementary and only the shared disjunct survives.

Parity is spelled `% 2 = 0` rather than `Even`, so that `Finset.filter` gets its
`DecidablePred` from `Nat.decEq` with nothing to synthesize.

The parity description has one decisive advantage over "list the blocks": it is
*local*, so it behaves well under both operations that the coboundary formula
needs -- deleting a vertex of the ambient simplex (`cutU_map_succAbove`, in
`SteenrodCutCancel.lean`) and inserting one new cut point (`mem_cutU_insert`).

## Degrees

`|u ⌣ᵢ v| = |u| + |v| - i` is a natural subtraction, and therefore a partial
function of the wrong shape for Lean.  Nothing here mentions it: the sum
defining `⌣ᵢ` runs over *all* `(i+1)`-element cut sets of the *output* simplex
(`cutIndex`), and the cardinality bookkeeping is discharged by the face
evaluation `faceVal` of `SteenrodCochain.lean`, which returns `0` on a subset
of the wrong size.  No subtraction occurs anywhere in this development.
-/

open CategoryTheory MonoidalCategory AlgebraicTopology Simplicial SimplexCategory

namespace GroupApproximation
namespace CharClass

/-! ## 1. The face map onto a set of vertices -/

/-- The simplex map `⦋k⦌ ⟶ ⦋m⦌` whose image is the vertex set `U`, listed in
increasing order.  This is the only way a face map is ever built below: a face
of a simplex *is* a subset of its vertices, and `Finset.orderEmbOfFin` is the
order-preserving enumeration of one. -/
def faceOfFinset {m k : ℕ} (U : Finset (Fin (m + 1))) (h : U.card = k + 1) :
    (⦋k⦌ : SimplexCategory) ⟶ ⦋m⦌ :=
  SimplexCategory.mkHom ⟨U.orderEmbOfFin h, (U.orderEmbOfFin h).monotone⟩

@[simp]
theorem faceOfFinset_apply {m k : ℕ} (U : Finset (Fin (m + 1))) (h : U.card = k + 1)
    (j : Fin (k + 1)) :
    (faceOfFinset U h).toOrderHom j = U.orderEmbOfFin h j :=
  rfl

/-- **Recognition lemma for face maps.**  A morphism of `SimplexCategory` that is
strictly monotone with all values in `U` *is* the face map onto `U`.  This is
`Finset.orderEmbOfFin_unique` transported across `mkHom`, and it is the only
place below where an equality of simplex maps is proved by hand. -/
theorem eq_faceOfFinset {m k : ℕ} (U : Finset (Fin (m + 1))) (h : U.card = k + 1)
    (f : (⦋k⦌ : SimplexCategory) ⟶ ⦋m⦌)
    (hmem : ∀ x, f.toOrderHom x ∈ U)
    (hmono : StrictMono (f.toOrderHom : Fin (k + 1) → Fin (m + 1))) :
    f = faceOfFinset U h := by
  have hfun : (f.toOrderHom : Fin (k + 1) → Fin (m + 1)) = U.orderEmbOfFin h :=
    Finset.orderEmbOfFin_unique h hmem hmono
  ext x : 3
  exact congrFun hfun x

/-- **Deleting a vertex of the face.**  Precomposing the face map onto `U` with
the `j`-th face map of the small simplex is the face map onto `U` with its
`j`-th element removed. -/
theorem delta_comp_faceOfFinset {m k : ℕ} (U : Finset (Fin (m + 1))) (h : U.card = k + 2)
    (j : Fin (k + 2)) :
    SimplexCategory.δ j ≫ faceOfFinset U h
      = faceOfFinset (U.erase (U.orderEmbOfFin h j))
          (by rw [Finset.card_erase_of_mem (U.orderEmbOfFin_mem h j), h]; rfl) := by
  refine eq_faceOfFinset _ _ _ (fun x => ?_) ?_
  · show U.orderEmbOfFin h (j.succAbove x) ∈ U.erase (U.orderEmbOfFin h j)
    refine Finset.mem_erase.2 ⟨fun hEq => ?_, U.orderEmbOfFin_mem h _⟩
    exact Fin.succAbove_ne j x ((U.orderEmbOfFin h).injective hEq)
  · show StrictMono fun x : Fin (k + 1) => U.orderEmbOfFin h (j.succAbove x)
    exact (U.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove j)

/-- **Deleting a vertex of the ambient simplex.**  Postcomposing the face map
onto `U` with the `i`-th face map of the big simplex is the face map onto the
image of `U` under the order embedding that skips `i`. -/
theorem faceOfFinset_comp_delta {m k : ℕ} (U : Finset (Fin (m + 1))) (h : U.card = k + 1)
    (i : Fin (m + 2)) :
    faceOfFinset U h ≫ SimplexCategory.δ i
      = faceOfFinset (U.map (Fin.succAboveOrderEmb i).toEmbedding)
          (by rw [Finset.card_map]; exact h) := by
  refine eq_faceOfFinset _ _ _ (fun x => ?_) ?_
  · show i.succAbove (U.orderEmbOfFin h x) ∈ U.map (Fin.succAboveOrderEmb i).toEmbedding
    exact Finset.mem_map_of_mem _ (U.orderEmbOfFin_mem h x)
  · show StrictMono fun x : Fin (k + 1) => i.succAbove (U.orderEmbOfFin h x)
    exact (Fin.strictMono_succAbove i).comp (U.orderEmbOfFin h).strictMono

/-! ## 2. Cuts -/

variable {N : ℕ}

/-- The number of cut points strictly below a vertex. -/
def cutRank (S : Finset (Fin N)) (x : Fin N) : ℕ :=
  (S.filter (fun c => c < x)).card

/-- The vertices handed to the **left** factor: those at even cut-rank,
together with the cut points themselves. -/
def cutU (S : Finset (Fin N)) : Finset (Fin N) :=
  Finset.univ.filter (fun x => x ∈ S ∨ cutRank S x % 2 = 0)

/-- The vertices handed to the **right** factor: those at odd cut-rank,
together with the cut points themselves. -/
def cutV (S : Finset (Fin N)) : Finset (Fin N) :=
  Finset.univ.filter (fun x => x ∈ S ∨ cutRank S x % 2 = 1)

@[simp]
theorem mem_cutU {S : Finset (Fin N)} {x : Fin N} :
    x ∈ cutU S ↔ x ∈ S ∨ cutRank S x % 2 = 0 := by
  simp [cutU]

@[simp]
theorem mem_cutV {S : Finset (Fin N)} {x : Fin N} :
    x ∈ cutV S ↔ x ∈ S ∨ cutRank S x % 2 = 1 := by
  simp [cutV]

theorem subset_cutU (S : Finset (Fin N)) : S ⊆ cutU S := fun _ hx => mem_cutU.2 (Or.inl hx)

theorem subset_cutV (S : Finset (Fin N)) : S ⊆ cutV S := fun _ hx => mem_cutV.2 (Or.inl hx)

/-- **The two families cover every vertex.**  A vertex not among the cut points
has some cut-rank, and its parity puts it in one family or the other. -/
theorem cutU_union_cutV (S : Finset (Fin N)) :
    cutU S ∪ cutV S = Finset.univ := by
  ext x
  simp only [Finset.mem_union, mem_cutU, mem_cutV, Finset.mem_univ, iff_true]
  rcases Nat.even_or_odd (cutRank S x) with h | h
  · exact Or.inl (Or.inr (Nat.even_iff.mp h))
  · exact Or.inr (Or.inr (Nat.odd_iff.mp h))

/-- **The two families overlap exactly in the cut points.**  The two parity
clauses are complementary, so only the shared disjunct `x ∈ S` survives. -/
theorem cutU_inter_cutV (S : Finset (Fin N)) :
    cutU S ∩ cutV S = S := by
  ext x
  simp only [Finset.mem_inter, mem_cutU, mem_cutV]
  constructor
  · rintro ⟨hU | hU, hV | hV⟩
    · exact hU
    · exact hU
    · exact hV
    · omega
  · intro hx
    exact ⟨Or.inl hx, Or.inl hx⟩

/-- A vertex outside the cut set lies in exactly one of the two families: if it
is in the left one it is not in the right one. -/
theorem not_mem_cutV_of_mem_cutU {S : Finset (Fin N)} {x : Fin N}
    (hxS : x ∉ S) (hx : x ∈ cutU S) : x ∉ cutV S := by
  intro hx'
  exact hxS (by rw [← cutU_inter_cutV S]; exact Finset.mem_inter.2 ⟨hx, hx'⟩)

/-- A vertex outside the cut set lies in exactly one of the two families: if it
is not in the left one it is in the right one. -/
theorem mem_cutV_of_not_mem_cutU {S : Finset (Fin N)} {x : Fin N}
    (hx : x ∉ cutU S) : x ∈ cutV S := by
  have := cutU_union_cutV S
  have hmem : x ∈ cutU S ∪ cutV S := by rw [this]; exact Finset.mem_univ x
  rcases Finset.mem_union.1 hmem with h | h
  · exact absurd h hx
  · exact h

/-- A vertex outside the cut set lies in exactly one of the two families: if it
is not in the right one it is in the left one. -/
theorem mem_cutU_of_not_mem_cutV {S : Finset (Fin N)} {x : Fin N}
    (hx : x ∉ cutV S) : x ∈ cutU S := by
  have := cutU_union_cutV S
  have hmem : x ∈ cutU S ∪ cutV S := by rw [this]; exact Finset.mem_univ x
  rcases Finset.mem_union.1 hmem with h | h
  · exact h
  · exact absurd h hx

/-- **The counting identity.**  `|U| + |V| = N + |S|`. -/
theorem cutU_card_add_cutV_card (S : Finset (Fin N)) :
    (cutU S).card + (cutV S).card = N + S.card := by
  have h := Finset.card_union_add_card_inter (cutU S) (cutV S)
  rw [cutU_union_cutV, cutU_inter_cutV] at h
  simpa [Finset.card_univ] using h.symm

/-! ## 3. The index set of an `i`-cut -/

/-- The **`i`-cuts of an `n`-simplex**: the `(i+1)`-element sets of cut points
among its `n+1` vertices.  No cardinality condition on the two families is
imposed here; it is enforced by `faceVal` in `SteenrodCochain.lean`, which
evaluates a cochain to `0` on a face of the wrong dimension. -/
def cutIndex (i n : ℕ) : Finset (Finset (Fin (n + 1))) :=
  (Finset.univ : Finset (Fin (n + 1))).powersetCard (i + 1)

@[simp]
theorem mem_cutIndex {i n : ℕ} {S : Finset (Fin (n + 1))} :
    S ∈ cutIndex i n ↔ S.card = i + 1 := by
  simp [cutIndex, Finset.mem_powersetCard, Finset.subset_univ]

theorem card_of_mem_cutIndex {i n : ℕ} {S : Finset (Fin (n + 1))} (hS : S ∈ cutIndex i n) :
    S.card = i + 1 :=
  mem_cutIndex.mp hS

/-- For an admissible bidegree, the right family has the complementary size, and
this is derived from the counting identity rather than imposed. -/
theorem cutV_card_of_cutU_card {i n a b : ℕ} {S : Finset (Fin (n + 1))}
    (hS : S ∈ cutIndex i n) (hab : a + b = n + i) (hU : (cutU S).card = a + 1) :
    (cutV S).card = b + 1 := by
  have hcount := cutU_card_add_cutV_card S
  rw [hU, card_of_mem_cutIndex hS] at hcount
  omega

end CharClass
end GroupApproximation
