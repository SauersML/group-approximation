import GroupApproximation.GGT.OsinTheorem54SepFinite

/-!
# Quasi-geodesic polygons in `Γ(G, X ⊔ ℋ)`, concretely

`OsinComponents.IsolatedComponentBound` quantifies over an *abstract* predicate
`IsQuasiGeodesicPolygon : ℝ → ℝ → ℕ → G → List (RelLetter G Λ) → Prop`, and
nothing in the repository defines one.  This module supplies the intended
instance and the fact that makes it usable.

* `IsQuasiGeodesicPolygon` --- a closed path (`listVal w = 1`) read from `v`,
  together with `n` cut points splitting it into sides, each side being
  `(μ,b)`-quasi-geodesic: along a side, the word distance between two vertices is
  at least `(j − i)/μ − b`.  Only the lower bound is asked for; the upper bound
  is automatic, consecutive vertices being one letter apart.
* `isQuasiGeodesicPolygon_nil` --- the predicate is inhabited, so
  `IsolatedComponentBound` is not a statement about an empty class.
* `sub_le_wordDist_vertex` --- **the fact the instance rests on: a sub-path of a
  geodesic word is geodesic.**  If `w` is a geodesic word from `f` to `g`, then
  `d(vertex i, vertex j) ≥ j − i` for `i ≤ j ≤ |w|`.  Cutting `w` at `i` and `j`
  writes `f⁻¹g` as a product of three pieces whose lengths are at most `i`, that
  distance, and `|w| − j`; the total is at least `|w| = d(f,g)`, and the two
  outer bounds leave the middle one no room.  So a geodesic side is
  `(1,0)`-quasi-geodesic, which is the case Osin's Lemma 4.2 is applied in.

What is still missing is not the predicate but the theorem: the bound
`d̂_λ(a₋,a₊) ≤ Cn` for an isolated component of such a polygon.  See
`GGT/OsinTheorem54SepRuns.lean` for why the uniform Morse lemma does not by
itself supply it --- the shortcut it produces need not avoid `Γ_{H_λ}`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Letters have letters' values -/

/-- The value of an admissible letter is a letter of the alphabet. -/
theorem val_mem_alphabet (D : RelGenSet G Λ) {a : RelLetter G Λ}
    (ha : D.IsLetter a) : a.val ∈ D.alphabet.carrier := by
  cases a with
  | base x => exact Set.mem_union_left _ ha
  | comp lam y => exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, ha⟩)

/-- A word of admissible letters bounds the word length of what it spells. -/
theorem wordNorm_listVal_le (D : RelGenSet G Λ) (u : List (RelLetter G Λ))
    (hu : ∀ a ∈ u, D.IsLetter a) :
    wordNorm D.alphabet.carrier (RelLetter.listVal u) ≤ u.length := by
  have hiw : IsWord D.alphabet.carrier (u.map RelLetter.val)
      (RelLetter.listVal u) := by
    refine ⟨?_, rfl⟩
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact val_mem_alphabet D (hu a ha)
  have hle := wordNorm_le_length hiw
  rwa [List.length_map] at hle

/-! ## Sub-paths of a geodesic word are geodesic -/

/-- **A geodesic side is `(1,0)`-quasi-geodesic.**

Cut `w` at `i` and at `j`.  The three pieces spell `f⁻¹·(vertex i)`,
`(vertex i)⁻¹·(vertex j)` and `(vertex j)⁻¹·g`, and have word lengths at most
`i`, `d`, and `|w| − j`.  Their product is `f⁻¹g`, whose word length is `|w|`
because `w` is geodesic.  So `|w| ≤ i + d + (|w| − j)`, which is `j − i ≤ d`. -/
theorem sub_le_wordDist_vertex (D : RelGenSet G Λ) {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ w.length) :
    j - i ≤ wordDist D.alphabet.carrier (vertex f w i) (vertex f w j) := by
  obtain ⟨hlet, hprod, hlen⟩ := hw
  have hpre : RelLetter.listVal (w.take i) = f⁻¹ * vertex f w i := by
    rw [vertex_eq_mul_listVal_take, inv_mul_cancel_left]
  have hprej : RelLetter.listVal (w.take j) = f⁻¹ * vertex f w j := by
    rw [vertex_eq_mul_listVal_take, inv_mul_cancel_left]
  have hsplit : RelLetter.listVal (w.take j) * RelLetter.listVal (w.drop j)
      = RelLetter.listVal w := by
    rw [← listVal_append, List.take_append_drop]
  have hlw : RelLetter.listVal w = f⁻¹ * g := by
    rw [← hprod]
    group
  have hsuf : RelLetter.listVal (w.drop j) = (vertex f w j)⁻¹ * g := by
    rw [hprej, hlw] at hsplit
    calc RelLetter.listVal (w.drop j)
        = (f⁻¹ * vertex f w j)⁻¹ *
            ((f⁻¹ * vertex f w j) * RelLetter.listVal (w.drop j)) := by group
      _ = (f⁻¹ * vertex f w j)⁻¹ * (f⁻¹ * g) := by rw [hsplit]
      _ = (vertex f w j)⁻¹ * g := by group
  have h1 : wordNorm D.alphabet.carrier (f⁻¹ * vertex f w i) ≤ i := by
    rw [← hpre]
    refine le_trans
      (wordNorm_listVal_le D (w.take i)
        (fun a ha => hlet a (List.take_subset i w ha))) ?_
    rw [List.length_take]
    omega
  have h2 : wordNorm D.alphabet.carrier ((vertex f w j)⁻¹ * g)
      ≤ w.length - j := by
    rw [← hsuf]
    refine le_trans
      (wordNorm_listVal_le D (w.drop j)
        (fun a ha => hlet a (List.drop_subset j w ha))) ?_
    rw [List.length_drop]
  have he : f⁻¹ * g = (f⁻¹ * vertex f w i) *
      ((vertex f w i)⁻¹ * vertex f w j) * ((vertex f w j)⁻¹ * g) := by group
  -- the two subadditivity steps must be stated at `D.alphabet.carrier`, not at
  -- the unfolded union, or `omega` sees two unrelated atoms
  have hab := wordNorm_mul_le D.alphabet.symmetricGenerating
    ((f⁻¹ * vertex f w i) * ((vertex f w i)⁻¹ * vertex f w j))
    ((vertex f w j)⁻¹ * g)
  have hcd := wordNorm_mul_le D.alphabet.symmetricGenerating
    (f⁻¹ * vertex f w i) ((vertex f w i)⁻¹ * vertex f w j)
  have hfg : wordNorm D.alphabet.carrier (f⁻¹ * g) = w.length := by
    rw [hlen]
    rfl
  rw [he] at hfg
  have hdd : wordDist D.alphabet.carrier (vertex f w i) (vertex f w j)
      = wordNorm D.alphabet.carrier ((vertex f w i)⁻¹ * vertex f w j) := rfl
  rw [hdd]
  omega

/-! ## The polygon predicate -/

/-- **A `(μ,b)`-quasi-geodesic `n`-gon in `Γ(G, X ⊔ ℋ)`**: a closed path read
from `v`, cut into `n` sides, each side quasi-geodesic.

The cut points are given by a monotone `c` with `c 0 = 0` and `c n = |w|`.  Only
the lower bound on distances is imposed: the upper bound `d ≤ j − i` is automatic
in a Cayley graph, consecutive vertices being one letter apart.

This is the predicate `OsinComponents.IsolatedComponentBound` is meant to be
instantiated at. -/
def IsQuasiGeodesicPolygon (D : RelGenSet G Λ) (μ b : ℝ) (n : ℕ) (v : G)
    (w : List (RelLetter G Λ)) : Prop :=
  (∀ a ∈ w, D.IsLetter a) ∧ RelLetter.listVal w = 1 ∧
    ∃ c : ℕ → ℕ, c 0 = 0 ∧ c n = w.length ∧ (∀ s : ℕ, c s ≤ c (s + 1)) ∧
      ∀ s : ℕ, s < n → ∀ i j : ℕ, c s ≤ i → i ≤ j → j ≤ c (s + 1) →
        ((j - i : ℕ) : ℝ) / μ - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w i) (vertex v w j) : ℕ) : ℝ)

/-- **The predicate is inhabited**, so `IsolatedComponentBound` is not a
statement about an empty class.  The degenerate polygon is the empty path. -/
theorem isQuasiGeodesicPolygon_nil (D : RelGenSet G Λ) {μ b : ℝ} (hb : 0 ≤ b)
    (v : G) : IsQuasiGeodesicPolygon D μ b 1 v [] := by
  refine ⟨by simp, RelLetter.listVal_nil, fun _ => 0, rfl, by simp, fun _ => le_rfl,
    ?_⟩
  intro s _ i j _ hij hj
  -- the cut function is a lambda, so `hj` reaches `omega` unreduced; the
  -- ascription beta-reduces it
  have hj0 : j = 0 := Nat.le_zero.mp hj
  have hi0 : i = 0 := by omega
  subst hi0
  subst hj0
  have hzero : ((0 - 0 : ℕ) : ℝ) / μ = 0 := by norm_num
  rw [hzero]
  have hnn : (0 : ℝ)
      ≤ ((wordDist D.alphabet.carrier
        (vertex v ([] : List (RelLetter G Λ)) 0)
        (vertex v ([] : List (RelLetter G Λ)) 0) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  linarith

end OsinComponents
end GGT
end GroupApproximation
