import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.AlexanderWhitneyChainMap
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset

/-!
# The combinatorics of Steenrod's cup-`i` products: `i`-cuts

Steenrod's `⌣ᵢ` is a sum over ways of splitting the vertices of a simplex into
two overlapping alternating families.  This file builds that index set and the
two face maps it produces, and nothing else: no cochains appear here, so the
whole file is finite combinatorics of `Finset (Fin (m+1))`.

## The picture

Fix `m` and cut points `c₀ < c₁ < ⋯ < cᵢ` among the vertices `0,…,m`.  They
split the vertex set into alternating blocks, which are handed out to the two
factors:

```text
U = [0,c₀] ∪ [c₁,c₂] ∪ [c₃,c₄] ∪ ⋯
V =         [c₀,c₁] ∪ [c₂,c₃] ∪ ⋯
```

`U` and `V` cover everything and meet exactly in the `i+1` cut points, so

```text
|U| + |V| = (m+1) + (i+1).
```

`cutU_union_cutV` and `cutU_inter_cutV` are those two sentences, and
`cutU_card_add_cutV_card` is their consequence.  A cut is *admissible* for
`(i,p,q)` when `|U| = p+i+1`, and then `|V| = q+i+1` follows
(`cutV_card_of_mem_cuts`) rather than being imposed.

## Why the membership test is a parity

Writing `cutRank S x` for the number of cut points strictly below `x`, a vertex
lies in `U` exactly when that count is even, and in `V` exactly when it is odd
-- *except* that the cut points themselves lie in both, which is what makes the
two families overlap.  So both tests are "`x` is a cut point, or the parity is
right", which is why `cutU_inter_cutV` collapses to `S` on the nose: the parity
clauses are complementary and only the shared disjunct survives.

Parity is spelled `% 2 = 0` rather than `Even`, so that `Finset.filter` gets its
`DecidablePred` from `Nat.decEq` with nothing to synthesize.

## Degrees

`|u ⌣ᵢ v| = |u| + |v| - i`, which is a natural subtraction and therefore a
partial function of the wrong shape for Lean.  Everything here is indexed by
the *shifted* degrees instead: a cut for `(i,p,q)` cuts a simplex of dimension
`p+q+i` into a face of dimension `p+i` and a face of dimension `q+i`.  No
subtraction occurs anywhere in this file or in anything built on it, and `i = 0`
is the ordinary Alexander--Whitney splitting.
-/

open CategoryTheory MonoidalCategory AlgebraicTopology Simplicial SimplexCategory

namespace GroupApproximation
namespace AlgTop

/-! ## The face map onto a set of vertices -/

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

/-! ## Cuts -/

variable {m : ℕ}

/-- The number of cut points strictly below a vertex. -/
def cutRank (S : Finset (Fin (m + 1))) (x : Fin (m + 1)) : ℕ :=
  (S.filter (fun c => c < x)).card

/-- The vertices handed to the **left** factor: those at even cut-rank,
together with the cut points themselves. -/
def cutU (S : Finset (Fin (m + 1))) : Finset (Fin (m + 1)) :=
  Finset.univ.filter (fun x => x ∈ S ∨ cutRank S x % 2 = 0)

/-- The vertices handed to the **right** factor: those at odd cut-rank,
together with the cut points themselves. -/
def cutV (S : Finset (Fin (m + 1))) : Finset (Fin (m + 1)) :=
  Finset.univ.filter (fun x => x ∈ S ∨ cutRank S x % 2 = 1)

@[simp]
theorem mem_cutU {S : Finset (Fin (m + 1))} {x : Fin (m + 1)} :
    x ∈ cutU S ↔ x ∈ S ∨ cutRank S x % 2 = 0 := by
  simp [cutU]

@[simp]
theorem mem_cutV {S : Finset (Fin (m + 1))} {x : Fin (m + 1)} :
    x ∈ cutV S ↔ x ∈ S ∨ cutRank S x % 2 = 1 := by
  simp [cutV]

/-- **The two families cover every vertex.**  A vertex not among the cut points
has some cut-rank, and its parity puts it in one family or the other. -/
theorem cutU_union_cutV (S : Finset (Fin (m + 1))) :
    cutU S ∪ cutV S = Finset.univ := by
  ext x
  simp only [Finset.mem_union, mem_cutU, mem_cutV, Finset.mem_univ, iff_true]
  rcases Nat.even_or_odd (cutRank S x) with h | h
  · exact Or.inl (Or.inr (Nat.even_iff.mp h))
  · exact Or.inr (Or.inr (Nat.odd_iff.mp h))

/-- **The two families overlap exactly in the cut points.**  The two parity
clauses are complementary, so only the shared disjunct `x ∈ S` survives. -/
theorem cutU_inter_cutV (S : Finset (Fin (m + 1))) :
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

/-- **The counting identity.**  `|U| + |V| = (m+1) + |S|`. -/
theorem cutU_card_add_cutV_card (S : Finset (Fin (m + 1))) :
    (cutU S).card + (cutV S).card = (m + 1) + S.card := by
  have h := Finset.card_union_add_card_inter (cutU S) (cutV S)
  rw [cutU_union_cutV, cutU_inter_cutV] at h
  simpa [Finset.card_univ] using h.symm

/-! ## Admissible cuts for a bidegree -/

/-- The **`i`-cuts of a `(p+q+i)`-simplex adapted to the bidegree `(p,q)`**: the
`(i+1)`-element sets of cut points whose left family has exactly `p+i+1`
vertices.  The right family then automatically has `q+i+1`. -/
def cuts (i p q : ℕ) : Finset (Finset (Fin (p + q + i + 1))) :=
  (Finset.powersetCard (i + 1) (Finset.univ : Finset (Fin (p + q + i + 1)))).filter
    (fun S => (cutU S).card = p + i + 1)

theorem mem_cuts_iff {i p q : ℕ} {S : Finset (Fin (p + q + i + 1))} :
    S ∈ cuts i p q ↔ S.card = i + 1 ∧ (cutU S).card = p + i + 1 := by
  simp [cuts, Finset.mem_powersetCard, Finset.subset_univ]

theorem card_of_mem_cuts {i p q : ℕ} {S : Finset (Fin (p + q + i + 1))}
    (hS : S ∈ cuts i p q) : S.card = i + 1 :=
  (mem_cuts_iff.mp hS).1

theorem cutU_card_of_mem_cuts {i p q : ℕ} {S : Finset (Fin (p + q + i + 1))}
    (hS : S ∈ cuts i p q) : (cutU S).card = p + i + 1 :=
  (mem_cuts_iff.mp hS).2

/-- **The right family has the complementary size**, and this is derived from
the counting identity rather than imposed. -/
theorem cutV_card_of_mem_cuts {i p q : ℕ} {S : Finset (Fin (p + q + i + 1))}
    (hS : S ∈ cuts i p q) : (cutV S).card = q + i + 1 := by
  have hcount := cutU_card_add_cutV_card S
  rw [cutU_card_of_mem_cuts hS, card_of_mem_cuts hS] at hcount
  omega

/-! ## The two faces cut out -/

/-- The **left face** of an admissible cut: a face of dimension `p+i`. -/
def cutFrontFace {i p q : ℕ} {S : Finset (Fin (p + q + i + 1))} (hS : S ∈ cuts i p q) :
    (⦋p + i⦌ : SimplexCategory) ⟶ ⦋p + q + i⦌ :=
  faceOfFinset (cutU S) (cutU_card_of_mem_cuts hS)

/-- The **right face** of an admissible cut: a face of dimension `q+i`. -/
def cutBackFace {i p q : ℕ} {S : Finset (Fin (p + q + i + 1))} (hS : S ∈ cuts i p q) :
    (⦋q + i⦌ : SimplexCategory) ⟶ ⦋p + q + i⦌ :=
  faceOfFinset (cutV S) (cutV_card_of_mem_cuts hS)

end AlgTop
end GroupApproximation
