import GroupApproximation.GGT.OsinTheorem54SepPolygonVertex

/-!
# A quadrilateral, and where a component of one side can be connected

The configuration is Osin's and Dahmani--Guirardel--Osin's: a quadrilateral
`p q r (revWord s)` in `Γ(G, X ⊔ ℋ)`, closing because
`listVal s = listVal p * listVal q * listVal r`, with `q` and `s` the two long
sides and `p`, `r` the two short ones.  A component of the side `q` is a run of
`H_λ`-letters, and the question is what it can be connected to.

## What is proved here

* `vertex_fourGon_side`, `vertex_fourGon_opposite_closed` --- the two vertex
  addresses.  The second is the one that pays: at index
  `|p| + |q| + |r| + (|s| - j)` the quadrilateral is at `vertex 1 s j`
  *exactly*, the translation `(listVal s)⁻¹` cancelling against the closing
  relation.  So the fourth side is read in its own coordinates.
* `connected_fourGon_iff` and `exists_connector_fourGon` --- a component of `q`
  connected to a component of `s` **names its connector**: an explicit
  `h ∈ H_λ` with `listVal p * vertex 1 q i * h = vertex 1 s j`.
* `fourGon_index_cases` --- an index of the quadrilateral lies in one of the
  four sides.
* `not_isCompStart_fourGon_first`, `not_isCompStart_fourGon_third` --- if the
  two short sides are spelled by base letters, they carry **no components at
  all**, so two of those four cases are empty.
* `exists_other_component_fourGon` --- the isolated-component form: a
  non-isolated component of `q` is connected either to another component of `q`
  itself, or to a component of `s`, and in the second case with the named
  connector.

## What is *not* proved here, and why the disjunction stays

The first branch is not empty in general.  For `(μ,b)`-quasi-geodesic sides
with `μ(1 + b) ≥ 2` a side can have two of its own components connected: the
side `[comp λ h₁, base x, comp λ h₂]` with `x ∈ X ∩ H_λ` is `(3,0)`-quasi-
geodesic and its two components are connected.  Only for `μ(1 + b) < 2` --- in
particular for geodesic sides --- does that branch close.  Bounding the
connector, which is Dahmani--Guirardel--Osin's Proposition 4.13, is a further
statement again, and is not attempted here: no bound on `h` is claimed.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The two vertex addresses -/

/-- **A vertex of the side `q`**, at index `|p| + i` of the quadrilateral. -/
theorem vertex_fourGon_side (p q r s : List (RelLetter G Λ)) (v : G) {i : ℕ}
    (hi : i ≤ q.length) :
    vertex v (p ++ q ++ r ++ revWord s) (p.length + i)
      = v * RelLetter.listVal p * vertex (1 : G) q i := by
  have h1 : p.length + i ≤ (p ++ q ++ r).length := by
    rw [List.length_append, List.length_append]
    omega
  have h2 : p.length + i ≤ (p ++ q).length := by
    rw [List.length_append]
    omega
  rw [vertex_append_of_le _ _ _ _ h1, vertex_append_of_le _ _ _ _ h2,
    vertex_append_add p q v i,
    vertex_eq_mul_vertex_one q (v * RelLetter.listVal p) i]

/-- **A vertex of the reversed side `s`**, before the closing relation is
used. -/
theorem vertex_fourGon_opposite (p q r s : List (RelLetter G Λ)) (v : G)
    (j : ℕ) :
    vertex v (p ++ q ++ r ++ revWord s)
        (p.length + q.length + r.length + (s.length - j))
      = v * RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r
          * (RelLetter.listVal s)⁻¹ * vertex (1 : G) s j := by
  have hlenA : (p ++ q ++ r).length = p.length + q.length + r.length := by
    rw [List.length_append, List.length_append]
  have hvalA : RelLetter.listVal (p ++ q ++ r)
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r := by
    rw [listVal_append, listVal_append]
  rw [← hlenA, vertex_append_add, hvalA, vertex_revWord]
  group

/-- **The fourth side is read in its own coordinates.**

This is the step the whole quadrilateral argument turns on: once the
quadrilateral closes, the translation `(listVal s)⁻¹` of `vertex_revWord`
cancels against `listVal p * listVal q * listVal r`, and the vertex of the
polygon at index `|p| + |q| + |r| + (|s| - j)` is *equal* to `vertex 1 s j`,
not merely a translate of it. -/
theorem vertex_fourGon_opposite_closed (p q r s : List (RelLetter G Λ))
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    (j : ℕ) :
    vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + q.length + r.length + (s.length - j))
      = vertex (1 : G) s j := by
  rw [vertex_fourGon_opposite, one_mul, ← hclose, mul_inv_cancel, one_mul]

/-! ## The connector between the two long sides -/

/-- **Connectedness across the quadrilateral, in the coordinates of the two
long sides.** -/
theorem connected_fourGon_iff (D : RelGenSet G Λ) (lam : Λ)
    (p q r s : List (RelLetter G Λ))
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    {i j : ℕ} (hi : i ≤ q.length) :
    Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i)
        (p.length + q.length + r.length + (s.length - j))
      ↔ (RelLetter.listVal p * vertex (1 : G) q i)⁻¹ * vertex (1 : G) s j
          ∈ D.fam lam := by
  show (vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + i))⁻¹ *
      vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + q.length + r.length + (s.length - j)) ∈ D.fam lam ↔ _
  rw [vertex_fourGon_side p q r s 1 hi,
    vertex_fourGon_opposite_closed p q r s hclose j, one_mul]

/-- **The connector is named.**

A component of `q` at index `i` connected to a component of `s` at index `j`
gives an explicit `h ∈ H_λ` with
`listVal p * vertex 1 q i * h = vertex 1 s j`: the short side `p` translates
the vertex of `q` to the polygon, and `h` closes the gap to the vertex of `s`.

No bound on `h` is asserted, and none is available from this argument alone. -/
theorem exists_connector_fourGon (D : RelGenSet G Λ) (lam : Λ)
    (p q r s : List (RelLetter G Λ))
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    {i j : ℕ} (hi : i ≤ q.length)
    (hconn : Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i)
      (p.length + q.length + r.length + (s.length - j))) :
    ∃ h : G, h ∈ D.fam lam ∧
      RelLetter.listVal p * vertex (1 : G) q i * h = vertex (1 : G) s j := by
  refine ⟨(RelLetter.listVal p * vertex (1 : G) q i)⁻¹ * vertex (1 : G) s j,
    (connected_fourGon_iff D lam p q r s hclose hi).mp hconn, ?_⟩
  group

/-! ## Which side an index lies in -/

/-- **The four sides cover the indices.**  The ranges overlap at the corners,
which is harmless: what is needed is that every index is accounted for. -/
theorem fourGon_index_cases (p q r s : List (RelLetter G Λ)) {n : ℕ}
    (hn : n ≤ (p ++ q ++ r ++ revWord s).length) :
    n < p.length ∨
      (∃ i : ℕ, i ≤ q.length ∧ n = p.length + i) ∨
      (∃ m : ℕ, m < r.length ∧ n = p.length + q.length + m) ∨
      (∃ j : ℕ, j ≤ s.length ∧
        n = p.length + q.length + r.length + (s.length - j)) := by
  rw [length_fourGon] at hn
  by_cases h1 : n < p.length
  · exact Or.inl h1
  · by_cases h2 : n ≤ p.length + q.length
    · exact Or.inr (Or.inl ⟨n - p.length, by omega, by omega⟩)
    · by_cases h3 : n < p.length + q.length + r.length
      · exact Or.inr (Or.inr (Or.inl
          ⟨n - (p.length + q.length), by omega, by omega⟩))
      · exact Or.inr (Or.inr (Or.inr
          ⟨s.length - (n - (p.length + q.length + r.length)), by omega,
            by omega⟩))

omit [Group G] in
/-- **A component starts on a component letter.** -/
theorem isCompOf_getElem_of_isCompStart {w : List (RelLetter G Λ)} {lam : Λ}
    {n : ℕ} (h : IsCompStart lam w n) :
    ∃ hn : n < w.length, (w[n]'hn).IsCompOf lam := by
  obtain ⟨k, hik, hkl, hall, -, -⟩ := h
  have hn : n < w.length := lt_of_lt_of_le hik hkl
  exact ⟨hn, hall n le_rfl hik hn⟩

omit [Group G] in
/-- **No component starts at a base letter.** -/
theorem not_isCompStart_of_base {w : List (RelLetter G Λ)} {lam : Λ} {n : ℕ}
    (hb : ∀ hn : n < w.length, ∃ x : G, (w[n]'hn) = RelLetter.base x) :
    ¬ IsCompStart lam w n := by
  intro h
  obtain ⟨hn, hcomp⟩ := isCompOf_getElem_of_isCompStart h
  obtain ⟨x, hx⟩ := hb hn
  rw [hx] at hcomp
  exact hcomp

/-- **A short side spelled by base letters carries no components.**  First
side. -/
theorem not_isCompStart_fourGon_first (p q r s : List (RelLetter G Λ))
    (lam : Λ) (hp : ∀ a ∈ p, ∃ x : G, a = RelLetter.base x) {n : ℕ}
    (hn : n < p.length) :
    ¬ IsCompStart lam (p ++ q ++ r ++ revWord s) n := by
  refine not_isCompStart_of_base ?_
  intro hn'
  have h1 : n < (p ++ q ++ r).length := by
    rw [List.length_append, List.length_append]
    omega
  have h2 : n < (p ++ q).length := by
    rw [List.length_append]
    omega
  have hmem : (p ++ q ++ r ++ revWord s)[n]'hn' ∈ p := by
    rw [List.getElem_append_left h1, List.getElem_append_left h2,
      List.getElem_append_left hn]
    exact List.getElem_mem _
  exact hp _ hmem

/-- **A short side spelled by base letters carries no components.**  Third
side. -/
theorem not_isCompStart_fourGon_third (p q r s : List (RelLetter G Λ))
    (lam : Λ) (hr : ∀ a ∈ r, ∃ x : G, a = RelLetter.base x) {m : ℕ}
    (hm : m < r.length) :
    ¬ IsCompStart lam (p ++ q ++ r ++ revWord s)
      (p.length + q.length + m) := by
  refine not_isCompStart_of_base ?_
  intro hn'
  have h1 : p.length + q.length + m < (p ++ q ++ r).length := by
    rw [List.length_append, List.length_append]
    omega
  have h2 : (p ++ q).length ≤ p.length + q.length + m := by
    rw [List.length_append]
    omega
  have hmem : (p ++ q ++ r ++ revWord s)[p.length + q.length + m]'hn' ∈ r := by
    rw [List.getElem_append_left h1, List.getElem_append_right h2]
    exact List.getElem_mem _
  exact hr _ hmem

/-! ## The isolated-component form -/

/-- **A non-isolated component of the long side `q` is connected either to
another component of `q` or to a component of the opposite side `s`**, and in
the second case its connector is named.

The two short sides are excluded because they are spelled by base letters and
so carry no components at all.  The first branch cannot be excluded in this
generality: two components of one `(μ,b)`-quasi-geodesic side can be connected
once `μ(1 + b) ≥ 2`.  And no bound on the connector is claimed --- that is
Dahmani--Guirardel--Osin's Proposition 4.13, a separate statement. -/
theorem exists_other_component_fourGon (D : RelGenSet G Λ) (lam : Λ)
    (p q r s : List (RelLetter G Λ))
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    (hp : ∀ a ∈ p, ∃ x : G, a = RelLetter.base x)
    (hr : ∀ a ∈ r, ∃ x : G, a = RelLetter.base x)
    {i : ℕ} (hi : i ≤ q.length)
    (hstart : IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i))
    (hnot : ¬ IsIsolated D.fam lam 1 (p ++ q ++ r ++ revWord s)
      (p.length + i)) :
    (∃ i' : ℕ, i' ≤ q.length ∧ i' ≠ i ∧
        IsCompStart lam (p ++ q ++ r ++ revWord s) (p.length + i') ∧
        Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i)
          (p.length + i'))
      ∨ (∃ j : ℕ, j ≤ s.length ∧
        IsCompStart lam (p ++ q ++ r ++ revWord s)
          (p.length + q.length + r.length + (s.length - j)) ∧
        ∃ h : G, h ∈ D.fam lam ∧
          RelLetter.listVal p * vertex (1 : G) q i * h
            = vertex (1 : G) s j) := by
  have hB : ¬ ∀ n : ℕ, n ≠ p.length + i →
      IsCompStart lam (p ++ q ++ r ++ revWord s) n →
        ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i) n := by
    intro hall
    exact hnot ⟨hstart, hall⟩
  push Not at hB
  obtain ⟨n, hne, hnstart, hnconn⟩ := hB
  obtain ⟨hnlt, -⟩ := isCompOf_getElem_of_isCompStart hnstart
  rcases fourGon_index_cases p q r s (le_of_lt hnlt) with
    hc | ⟨i', hi', rfl⟩ | ⟨m, hm, rfl⟩ | ⟨j, hj, rfl⟩
  · exact absurd hnstart (not_isCompStart_fourGon_first p q r s lam hp hc)
  · exact Or.inl ⟨i', hi', by omega, hnstart, hnconn⟩
  · exact absurd hnstart (not_isCompStart_fourGon_third p q r s lam hr hm)
  · exact Or.inr ⟨j, hj, hnstart,
      exists_connector_fourGon D lam p q r s hclose hi hnconn⟩

end OsinComponents
end GGT
end GroupApproximation
