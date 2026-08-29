import GroupApproximation.GGT.OsinTheorem54SepOrder

/-!
# Enumerating the separating cosets along a geodesic

Lemma 5.10's left half counts: a geodesic from `f` to `g` decomposes into
`|S(f,g;D)| + 1` gaps and `|S(f,g;D)| ` crossings, giving `2|S| + 1`.  To run
that count the separating cosets have to be enumerated IN ORDER, and this
module supplies the enumeration.

## The shape, and why it is indices rather than cosets

The obvious move is to sort `S(f,g;D)` itself by `SepLT`, which needs a
`DecidableRel` for a relation defined by an existential over geodesics --- so
classical choice, and then every lemma about the sorted list is about an order
nobody can compute with.

Instead, fix the geodesic and sort the INDICES at which it penetrates.  Those
form a set of naturals, so the linear order is `ℕ`'s, `Finset.sort` applies with
no choice and no new instance, and `SepLT` becomes literally `<` on indices.
The bridge back is a bijection:

* `penetratesAt_unique` (from `SepOrder`) makes index-to-coset injective ---
  a geodesic penetrates each coset at most once;
* the penetration half of `LemmaFourEight` makes it surjective onto
  `S(f,g;D)` --- every separating coset is penetrated by every geodesic.

so `sepCard_eq_ncard_sepIndexSet` says the count may be taken on either side.

## Model test

At `G = ⟨a⟩ * ⟨b⟩`, `H = ⟨a⟩`, `X = {b^±1}`, `f = 1`, `g = aba`, with geodesic
`[comp a, base b, comp a]`: the components are `[0,1)` and `[2,3)`, both
essential, so `sepIndexSet = {0, 2}`, of cardinality two, matching
`S(1,aba;Dc) = {H, abH}`.  Sorted it is `[0, 2]`, its one gap is the segment
from `1` to `2` spelling `b`, and the count `2·2 + 1 = 5` bounds the actual
`wordDist` of `3`.

Conditional on `LemmaFourEight` exactly where surjectivity is used.

One naming note, since `-DwarningAsError=true` makes it fatal rather than
cosmetic: `Set.ncard_image_of_injOn` is **deprecated** at this Mathlib revision
(2026-01-30) in favour of `Set.InjOn.ncard_image`, which is what the count below
uses.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The indices at which a fixed geodesic penetrates the separating
cosets.** -/
def sepIndexSet (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ) (f g : G)
    (w : List (RelLetter G Λ)) : Set ℕ :=
  {n | ∃ c, c ∈ sepSet D lam Dc f g ∧ PenetratesAt D lam Dc f w n c}

/-- Every penetration index lies inside the word. -/
theorem sepIndexSet_subset (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ) (f g : G)
    (w : List (RelLetter G Λ)) :
    sepIndexSet D lam Dc f g w ⊆ {n : ℕ | n < w.length} := by
  rintro n ⟨c, -, ⟨⟨k, hEP⟩, -⟩⟩
  obtain ⟨hnk, hkw, -, -, -⟩ := hEP.1
  exact lt_of_lt_of_le hnk hkw

/-- The index set is finite. -/
theorem sepIndexSet_finite (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ) (f g : G)
    (w : List (RelLetter G Λ)) :
    (sepIndexSet D lam Dc f g w).Finite :=
  (Set.finite_Iio w.length).subset (sepIndexSet_subset D lam Dc f g w)

/-- **Index to coset is injective**, a geodesic penetrating each coset once. -/
theorem injOn_sepIndexSet (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ) {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) :
    Set.InjOn (fun n : ℕ => (QuotientGroup.mk (vertex f w n) : G ⧸ D.fam lam))
      (sepIndexSet D lam Dc f g w) := by
  rintro n₁ ⟨c₁, -, hP₁⟩ n₂ ⟨c₂, -, hP₂⟩ heq
  refine penetratesAt_unique hw (c := c₁) hP₁ ?_
  have hc : c₁ = c₂ := by
    rw [hP₁.2, hP₂.2]
    exact heq
  rw [hc]
  exact hP₂

/-- **Index to coset is onto the separating set**, by the penetration half of
Lemma 4.8. -/
theorem sepSet_eq_image (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ)
    (h48 : LemmaFourEight D lam Dc) {f g : G} {w : List (RelLetter G Λ)}
    (hw : IsGeodesicWord D f g w) :
    sepSet D lam Dc f g
      = (fun n : ℕ => (QuotientGroup.mk (vertex f w n) : G ⧸ D.fam lam)) ''
        sepIndexSet D lam Dc f g w := by
  refine Set.Subset.antisymm ?_ ?_
  · intro c hc
    obtain ⟨n, k, hEP, hceq⟩ := h48.1 f g w hw c hc
    exact ⟨n, ⟨c, hc, ⟨⟨k, hEP⟩, hceq⟩⟩, hceq.symm⟩
  · rintro c ⟨n, ⟨c', hc', hP⟩, rfl⟩
    beta_reduce
    rw [← hP.2]
    exact hc'

/-- **The count may be taken on the indices.** -/
theorem sepCard_eq_ncard_sepIndexSet (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ)
    (h48 : LemmaFourEight D lam Dc) {f g : G} {w : List (RelLetter G Λ)}
    (hw : IsGeodesicWord D f g w) :
    sepCard D lam Dc f g = (sepIndexSet D lam Dc f g w).ncard := by
  show (sepSet D lam Dc f g).ncard = _
  rw [sepSet_eq_image D lam Dc h48 hw,
    Set.InjOn.ncard_image (injOn_sepIndexSet D lam Dc hw)]

end OsinComponents
end GGT
end GroupApproximation
