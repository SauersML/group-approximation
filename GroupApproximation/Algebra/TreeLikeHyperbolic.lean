import GroupApproximation.Algebra.HyperbolicInteger

/-!
# Tree-like word metrics are `0`-hyperbolic

`Kazhdan/SharpExistenceCertificateRoute.lean` reduces `SharpExistence` to two
finite objects: a rational Hodge certificate, and a concrete group that is
infinite, finitely presented, torsion-free and **hyperbolic**.  Of those four
clauses the last is the only one that is still mathematics here: the library
proves `IsHyperbolicGroup` for finite groups (bounded metric), for the trivial
group, and for `Multiplicative ℤ`, and for nothing else.

This module supplies the reusable engine for the tree case, which is the base
case of every combinatorial hyperbolicity argument --- free groups, free
products, and the Bass--Serre trees underneath small-cancellation quotients.

## The abstraction

`IsTreeLike S p` packages what a tree metric gives you: a symmetric *common
prefix length* `p x y` with

```
    d_S(x,y) + 2 p x y = |x|_S + |y|_S      (cancellation)
    min (p x z) (p y z) ≤ p x y             (ultrametric)
```

The first says that the geodesics from `1` to `x` and to `y` agree for exactly
`p x y` letters and are disjoint afterwards, which is precisely what happens in
a tree; the second says the agreement relation branches, never merges.

`isHyperbolicGroup_of_isTreeLike` turns those two lines into `δ = 0`
hyperbolicity.  The proof is short because `Algebra/HyperbolicGroup.lean`
already proves that the four-point condition *is* Gromov's product condition at
the same constant: under `IsTreeLike` the Gromov product is literally
`2 p (w⁻¹x) (w⁻¹y)`, by left invariance of the word metric, so the four-point
condition and the ultrametric inequality are the same statement.

Nothing here is specific to free groups.  What a free group would have to supply
is `p` --- the length of the longest common prefix of two reduced words --- and
the two displayed identities; the four-point condition then comes for free, and
that is the whole point of stating the abstraction separately.

## The control

`isTreeLike_intAlphabet` instantiates the abstraction on `Multiplicative ℤ`,
where the common prefix of `m` and `n` is `min |m| |n|` when they lie on the
same side of the origin and `0` otherwise.  It reproves
`isHyperbolicGroup_multiplicative_int`, which is already known by a direct
`omega` call --- the point is that the abstraction is inhabited and its two
axioms are the right ones, not that the line needed a new proof.
-/

namespace GroupApproximation
namespace Hyperbolic

open WordMetric

universe u

/-! ## The abstraction -/

/-- **A tree-like word metric**: a common-prefix length `p` satisfying the
cancellation identity and the ultrametric inequality.  See the module docstring
for what the two fields say geometrically. -/
structure IsTreeLike {G : Type u} [Group G] (S : Set G) (p : G → G → ℕ) : Prop where
  /-- Geodesics from the identity to `x` and to `y` share exactly `p x y`
  letters, so the distance between them is what is left over. -/
  split : ∀ x y : G, wordDist S x y + 2 * p x y = wordNorm S x + wordNorm S y
  /-- Agreement branches: if `z` agrees with both `x` and `y` for a while, then
  `x` and `y` agree with each other at least that long. -/
  ultra : ∀ x y z : G, min (p x z) (p y z) ≤ p x y

variable {G : Type u} [Group G] {S : Set G} {p : G → G → ℕ}

/-- A tree-like prefix length measures the whole of an element against
itself. -/
theorem IsTreeLike.self (h : IsTreeLike S p) (x : G) : p x x = wordNorm S x := by
  have hx := h.split x x
  rw [wordDist_self] at hx
  omega

/-- **The Gromov product of a tree-like metric is the common prefix length**,
based anywhere: left invariance moves the basepoint to the identity. -/
theorem twiceGromovProduct_eq_of_isTreeLike (h : IsTreeLike S p) (w x y : G) :
    twiceGromovProduct S w x y = 2 * (p (w⁻¹ * x) (w⁻¹ * y) : ℤ) := by
  have hwx : wordDist S w x = wordNorm S (w⁻¹ * x) := by
    have hinv := wordDist_left_invariant S w⁻¹ w x
    rw [inv_mul_cancel] at hinv
    rw [← hinv, wordDist_one_left]
  have hwy : wordDist S w y = wordNorm S (w⁻¹ * y) := by
    have hinv := wordDist_left_invariant S w⁻¹ w y
    rw [inv_mul_cancel] at hinv
    rw [← hinv, wordDist_one_left]
  have hxy : wordDist S x y = wordDist S (w⁻¹ * x) (w⁻¹ * y) :=
    (wordDist_left_invariant S w⁻¹ x y).symm
  have hsplit := h.split (w⁻¹ * x) (w⁻¹ * y)
  simp only [twiceGromovProduct, hwx, hwy, hxy]
  omega

/-- **A tree-like word metric satisfies the four-point condition at `δ = 0`.**
Through `isFourPointHyperbolic_iff_gromovProduct` the four-point condition is
exactly Gromov's product inequality, and under `IsTreeLike` that inequality is
the ultrametric field, doubled. -/
theorem isFourPointHyperbolic_zero_of_isTreeLike
    (hS : IsSymmetricGeneratingSet S) (h : IsTreeLike S p) :
    IsFourPointHyperbolic S 0 := by
  rw [isFourPointHyperbolic_iff_gromovProduct hS]
  intro w x y z
  rw [twiceGromovProduct_eq_of_isTreeLike h, twiceGromovProduct_eq_of_isTreeLike h,
    twiceGromovProduct_eq_of_isTreeLike h]
  have hu := h.ultra (w⁻¹ * x) (w⁻¹ * y) (w⁻¹ * z)
  omega

/-- **A group with a tree-like finite alphabet is hyperbolic**, at `δ = 0`. -/
theorem isHyperbolicGroup_of_isTreeLike {T : Finset G}
    (hT : IsSymmetricGeneratingSet (T : Set G)) {q : G → G → ℕ}
    (h : IsTreeLike (T : Set G) q) : IsHyperbolicGroup G :=
  ⟨T, hT, 0, isFourPointHyperbolic_zero_of_isTreeLike hT h⟩

/-! ## The control: the line is tree-like -/

/-- The word length of the infinite cyclic group, stated at a general element
rather than at `ofAdd`. -/
theorem wordNorm_intAlphabet (x : Multiplicative ℤ) :
    wordNorm intAlphabet x = (Multiplicative.toAdd x).natAbs := by
  simpa using wordNorm_ofAdd (Multiplicative.toAdd x)

/-- The common prefix length on the line: two integers on the same side of the
origin agree for `min |m| |n|` steps, and two on opposite sides agree for
none. -/
noncomputable def intPrefix (x y : Multiplicative ℤ) : ℕ :=
  if (0 ≤ Multiplicative.toAdd x ∧ 0 ≤ Multiplicative.toAdd y) ∨
      (Multiplicative.toAdd x ≤ 0 ∧ Multiplicative.toAdd y ≤ 0) then
    min (Multiplicative.toAdd x).natAbs (Multiplicative.toAdd y).natAbs
  else 0

/-- **The line is tree-like.**  Both axioms are integer arithmetic once the word
metric is identified with the distance on `ℤ`. -/
theorem isTreeLike_intAlphabet : IsTreeLike intAlphabet intPrefix := by
  constructor
  · intro x y
    rw [wordDist_intAlphabet, wordNorm_intAlphabet, wordNorm_intAlphabet, intPrefix]
    split_ifs with hcase
    · rcases hcase with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
    · push Not at hcase
      omega
  · intro x y z
    simp only [intPrefix]
    split_ifs <;> omega

/-- The line is hyperbolic, through the abstraction rather than directly.  A
consistency check on `IsTreeLike`, not a new theorem: compare
`isHyperbolicGroup_multiplicative_int`. -/
theorem isHyperbolicGroup_multiplicative_int_of_isTreeLike :
    IsHyperbolicGroup (Multiplicative ℤ) := by
  refine isHyperbolicGroup_of_isTreeLike (T := intAlphabetFinset) ?_ (q := intPrefix) ?_
  · rw [coe_intAlphabetFinset]
    exact isSymmetricGeneratingSet_intAlphabet
  · rw [coe_intAlphabetFinset]
    exact isTreeLike_intAlphabet

end Hyperbolic
end GroupApproximation
