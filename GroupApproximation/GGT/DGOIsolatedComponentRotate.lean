import GroupApproximation.GGT.DGOIsolatedComponentBridge
import GroupApproximation.GGT.OsinTheorem54SepPolygonVertex

/-!
# Rotating a closed polygon to put a component first

Dahmani--Guirardel--Osin's Lemma 4.16 takes the distinguished component as the
*first* side of the polygon.  The recuts of `DGOIsolatedComponentRecut` and
`DGOIsolatedComponentStraddle` deliver it as the side `t + 1`, so a consumer
fixed at index `0` needs the closed word turned round at that corner:

    rotWord w i = w.drop i ++ w.take i ,   read from `vertex v w i` .

Nothing about a rotation is deep — but nothing about it is free either, because
the seam can merge two components of `w` into one component of the rotated word,
and because a component ending at `w.length` can continue past the basepoint.
Both are handled here rather than assumed away.

Concept grep before writing: `rotate`, `drop … ++ take` across the tree.
`List.rotate` appears only in osin-ah4's periodicity argument
(`OsinTheorem54SepFourGonMeet`, on `List.rotate_replicate`), never on
`RelLetter` words and never with vertices; no module turns a polygon round.
The vertex arithmetic is reused: `vertex_append_of_le`, `vertex_append_add`,
`vertex_eq_mul_vertex_one` (SepPolygonVertex), `vertex_take_eq` (SepFinite),
`vertex_drop_eq` (DGOIsolatedComponentBridge).

## The two things that can go wrong, and why they do not

*A component ending at `w.length`.*  If `[i, w.length)` is a component and `w[0]`
is a `lam`-letter, the run continues past the basepoint and `[0, k-i)` is not
maximal in the rotated word.  That configuration cannot occur under isolation:
the path is closed, so `vertex v w w.length = v = vertex v w 0`, hence the
component at `0` is `Connected` to the one at `i` — `notMem_wrap_of_isIsolated`
turns exactly that into the hypothesis `isComp_rotWord` needs.

*The seam.*  If `w`'s last and first letters are both `lam`-letters, two
components of `w` become one component of the rotated word.  This does not break
the isolation transfer: the merged component's start is still a component start
of `w` at the same vertex (`exists_isCompStart_of_rotWord`), so a connection in
the rotated word is a connection in `w`, which isolatedness forbids.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The rotated word -/

/-- **The closed word turned round at the index `i`.**  Read from
`vertex v w i`, it traverses the same edges in the same cyclic order. -/
def rotWord (w : List (RelLetter G Λ)) (i : ℕ) : List (RelLetter G Λ) :=
  w.drop i ++ w.take i

omit [Group G] in
/-- Rotation does not change the length. -/
theorem length_rotWord (w : List (RelLetter G Λ)) {i : ℕ} (hi : i ≤ w.length) :
    (rotWord w i).length = w.length := by
  show (w.drop i ++ w.take i).length = w.length
  rw [List.length_append, List.length_drop, List.length_take_of_le hi]
  omega

/-- Rotation does not change the letters. -/
theorem letters_rotWord (D : RelGenSet G Λ) {w : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ w, D.IsLetter a) (i : ℕ) :
    ∀ a ∈ rotWord w i, D.IsLetter a := by
  intro a ha
  have ha' : a ∈ w.drop i ++ w.take i := ha
  rcases List.mem_append.mp ha' with h | h
  · exact hlet a (List.drop_subset i w h)
  · exact hlet a (List.take_subset i w h)

/-- **A rotation of a closed word is closed.**  In a group `ab = 1` gives
`ba = 1`, and the two halves spell `a` and `b`. -/
theorem listVal_rotWord (w : List (RelLetter G Λ)) (i : ℕ)
    (hclosed : RelLetter.listVal w = 1) : RelLetter.listVal (rotWord w i) = 1 := by
  have h : RelLetter.listVal (w.take i) * RelLetter.listVal (w.drop i) = 1 := by
    rw [← listVal_append, List.take_append_drop, hclosed]
  show RelLetter.listVal (w.drop i ++ w.take i) = 1
  rw [listVal_append, mul_eq_one_iff_eq_inv.mp h, mul_inv_cancel]

/-- The endpoint of a closed word is its basepoint. -/
theorem vertex_length_of_closed (v : G) (w : List (RelLetter G Λ))
    (hclosed : RelLetter.listVal w = 1) : vertex v w w.length = v := by
  rw [vertex_eq_mul_listVal_take w v w.length, List.take_length, hclosed, mul_one]

/-! ## The vertices of the rotated word -/

/-- Before the seam, the rotated vertices are the vertices of `w` from `i` on. -/
theorem vertex_rotWord_le (v : G) (w : List (RelLetter G Λ)) {i : ℕ}
    (_hi : i ≤ w.length) (p : ℕ) (hp : p ≤ w.length - i) :
    vertex (vertex v w i) (rotWord w i) p = vertex v w (i + p) := by
  show vertex (vertex v w i) (w.drop i ++ w.take i) p = vertex v w (i + p)
  rw [vertex_append_of_le (w.drop i) (w.take i) (vertex v w i) p
      (by rw [List.length_drop]; exact hp),
    vertex_eq_mul_vertex_one (w.drop i) (vertex v w i) p, vertex_drop_eq]

/-- After the seam, they are the vertices of `w` before `i`, the basepoint being
where the closed path returns. -/
theorem vertex_rotWord_add (v : G) (w : List (RelLetter G Λ)) {i : ℕ}
    (_hi : i ≤ w.length) (hclosed : RelLetter.listVal w = 1) (p r : ℕ)
    (hpr : p = w.length - i + r) (hr : r ≤ i) :
    vertex (vertex v w i) (rotWord w i) p = vertex v w r := by
  have hend : vertex v w i * RelLetter.listVal (w.drop i) = v := by
    have h : RelLetter.listVal (w.take i) * RelLetter.listVal (w.drop i)
        = RelLetter.listVal w := by
      rw [← listVal_append, List.take_append_drop]
    rw [vertex_eq_mul_listVal_take w v i, mul_assoc, h, hclosed, mul_one]
  show vertex (vertex v w i) (w.drop i ++ w.take i) p = vertex v w r
  rw [show p = (w.drop i).length + r from by rw [List.length_drop]; omega,
    vertex_append_add (w.drop i) (w.take i) (vertex v w i) r, hend,
    vertex_take_eq v w i r hr]

/-! ## The letters of the rotated word -/

omit [Group G] in
/-- Before the seam, the rotated letters are those of `w` from `i` on. -/
theorem getElem_rotWord_lt (w : List (RelLetter G Λ)) {i : ℕ} (_hi : i ≤ w.length)
    (p q : ℕ) (hpq : q = i + p) (hpi : p < w.length - i)
    (hp : p < (rotWord w i).length) (hqw : q < w.length) :
    (rotWord w i)[p]'hp = w[q]'hqw := by
  have h1 : (rotWord w i)[p]? = w[q]? := by
    show (w.drop i ++ w.take i)[p]? = w[q]?
    rw [List.getElem?_append_left (by rw [List.length_drop]; omega),
      List.getElem?_drop, hpq]
  rw [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hqw] at h1
  exact Option.some.inj h1

omit [Group G] in
/-- After the seam, they are the letters of `w` before `i`. -/
theorem getElem_rotWord_add (w : List (RelLetter G Λ)) {i : ℕ} (_hi : i ≤ w.length)
    (p r : ℕ) (hpr : p = w.length - i + r) (hr : r < i)
    (hp : p < (rotWord w i).length) (hpw : r < w.length) :
    (rotWord w i)[p]'hp = w[r]'hpw := by
  have h1 : (rotWord w i)[p]? = w[r]? := by
    show (w.drop i ++ w.take i)[p]? = w[r]?
    rw [List.getElem?_append_right (by rw [List.length_drop]; omega),
      List.length_drop, show p - (w.length - i) = r from by omega,
      List.getElem?_take_of_lt hr]
  rw [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hpw] at h1
  exact Option.some.inj h1

/-! ## The distinguished component, at index `0` -/

/-- **A component reaching the end of a closed word cannot be followed, past the
basepoint, by another `lam`-letter — if it is isolated.**

The path is closed, so `vertex v w w.length = v = vertex v w 0`; a `lam`-letter at
`0` would start a component whose initial vertex is the component's own terminal
vertex, hence `Connected` to it, which isolatedness forbids.  This is the
hypothesis `isComp_rotWord` needs, and it is where closedness enters. -/
theorem notMem_wrap_of_isIsolated (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hclosed : RelLetter.listVal w = 1) {i k : ℕ} (hcomp : IsComp lam w i k)
    (hiso : IsIsolated D.fam lam v w i) (hi : 0 < i) :
    ∀ h0 : 0 < w.length, k = w.length → ¬ (w[0]'h0).IsCompOf lam := by
  intro h0 hk hc
  obtain ⟨i₀, k₀, hi₀le, hjk₀, hcomp₀⟩ :=
    exists_isComp_of_isCompOf lam w 0 h0 hc
  have hi₀ : i₀ = 0 := by omega
  have hstart : IsCompStart lam w 0 := by
    refine ⟨k₀, ?_⟩
    rw [← hi₀]
    exact hcomp₀
  have hspan : (vertex v w i)⁻¹ * vertex v w k ∈ D.fam lam :=
    span_mem_fam_of_isComp D v hlet hcomp
  refine hiso.2 0 (by omega) hstart ?_
  have hv : vertex v w k = vertex v w 0 := by
    rw [hk, vertex_length_of_closed v w hclosed, vertex_zero]
  rw [hv] at hspan
  exact hspan

omit [Group G] in
/-- **The component at the rotation point becomes the component at `0`.** -/
theorem isComp_rotWord (lam : Λ) {w : List (RelLetter G Λ)} {i k : ℕ}
    (hcomp : IsComp lam w i k) (hi : i ≤ w.length)
    (hwrap : ∀ h0 : 0 < w.length, k = w.length → ¬ (w[0]'h0).IsCompOf lam) :
    IsComp lam (rotWord w i) 0 (k - i) := by
  have hik : i < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have hrange := hcomp.2.2.1
  have hnext := hcomp.2.2.2.2
  have hlen : (rotWord w i).length = w.length := length_rotWord w hi
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro j _ hj2 hjw
    rw [getElem_rotWord_lt w hi j (i + j) rfl (by omega) hjw (by omega)]
    exact hrange (i + j) (by omega) (by omega) (by omega)
  · intro j hj
    exact absurd hj (by omega)
  · intro hk hc
    rcases Nat.lt_or_ge (k - i) (w.length - i) with hlt | hge
    · -- the letter at `k` of `w`, which maximality forbids
      rw [getElem_rotWord_lt w hi (k - i) k (by omega) hlt hk (by omega)] at hc
      exact hnext (by omega) hc
    · -- past the seam: the letter at `0` of `w`, which isolation forbids
      have hkk : k = w.length := by omega
      rw [getElem_rotWord_add w hi (k - i) 0 (by omega) (by omega) hk
        (by omega)] at hc
      exact hwrap (by omega) hkk hc

/-! ## Isolation -/

/-- **Every other component start of the rotated word comes from one of `w`, at
the same vertex.**

Before the seam the correspondence is `j ↦ i + j`; after it, `j ↦ j - (|w| - i)`.
The seam itself is the one place where two components of `w` can merge into one
of the rotated word, and the merged component's start is still a component start
of `w`: it is `0`, whose predecessor in `w` does not exist. -/
theorem exists_isCompStart_of_rotWord (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (_hlet : ∀ a ∈ w, D.IsLetter a)
    (hclosed : RelLetter.listVal w = 1) {i k : ℕ} (hcomp : IsComp lam w i k)
    {j : ℕ} (hjstart : IsCompStart lam (rotWord w i) j) (hj0 : j ≠ 0) :
    ∃ p : ℕ, IsCompStart lam w p ∧ p ≠ i ∧
      vertex (vertex v w i) (rotWord w i) j = vertex v w p := by
  have hik : i < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have hi : i ≤ w.length := by omega
  have hlen : (rotWord w i).length = w.length := length_rotWord w hi
  obtain ⟨j2, hj2⟩ := hjstart
  have hj12 : j < j2 := hj2.1
  have hj2len : j2 ≤ (rotWord w i).length := hj2.2.1
  have hjrange := hj2.2.2.1
  have hjprev := hj2.2.2.2.1
  have hjlen : j < (rotWord w i).length := by omega
  have hcj := hjrange j le_rfl hj12 hjlen
  have hj1len : j - 1 < (rotWord w i).length := by omega
  have hprevn := hjprev (j - 1) (by omega) hj1len
  rcases Nat.lt_or_ge j (w.length - i) with hlt | hge
  · -- before the seam
    rw [getElem_rotWord_lt w hi j (i + j) rfl hlt hjlen (by omega)] at hcj
    refine ⟨i + j, ?_, by omega, vertex_rotWord_le v w hi j (by omega)⟩
    obtain ⟨i₀, k₀, hi₀le, hjk₀, hcomp₀⟩ :=
      exists_isComp_of_isCompOf lam w (i + j) (by omega) hcj
    have hi₀ : i₀ = i + j := by
      by_contra hne
      have hprevw := hcomp₀.2.2.1 (i + (j - 1)) (by omega) (by omega) (by omega)
      rw [getElem_rotWord_lt w hi (j - 1) (i + (j - 1)) rfl (by omega) hj1len
        (by omega)] at hprevn
      exact hprevn hprevw
    exact ⟨k₀, by rw [← hi₀]; exact hcomp₀⟩
  · -- at or after the seam
    have hjr : j = w.length - i + (j - (w.length - i)) := by omega
    have hrlt : j - (w.length - i) < i := by omega
    rw [getElem_rotWord_add w hi j (j - (w.length - i)) hjr hrlt hjlen
      (by omega)] at hcj
    refine ⟨j - (w.length - i), ?_, by omega,
      vertex_rotWord_add v w hi hclosed j (j - (w.length - i)) hjr (by omega)⟩
    obtain ⟨i₀, k₀, hi₀le, hjk₀, hcomp₀⟩ :=
      exists_isComp_of_isCompOf lam w (j - (w.length - i)) (by omega) hcj
    have hi₀ : i₀ = j - (w.length - i) := by
      rcases Nat.eq_zero_or_pos (j - (w.length - i)) with h0 | hpos
      · -- the seam itself: the run starts at `0` of `w`, which has no predecessor
        omega
      · by_contra hne
        have hprevw := hcomp₀.2.2.1 (j - (w.length - i) - 1) (by omega) (by omega)
          (by omega)
        rw [getElem_rotWord_add w hi (j - 1) (j - (w.length - i) - 1) (by omega)
          (by omega) hj1len (by omega)] at hprevn
        exact hprevn hprevw
    exact ⟨k₀, by rw [← hi₀]; exact hcomp₀⟩

/-- **Rotation preserves isolatedness of the distinguished component.** -/
theorem isIsolated_rotWord (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hclosed : RelLetter.listVal w = 1) {i k : ℕ} (hcomp : IsComp lam w i k)
    (hiso : IsIsolated D.fam lam v w i) (_hi : 0 < i)
    (hwrap : ∀ h0 : 0 < w.length, k = w.length → ¬ (w[0]'h0).IsCompOf lam) :
    IsIsolated D.fam lam (vertex v w i) (rotWord w i) 0 := by
  have hik : i < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have hiw : i ≤ w.length := by omega
  refine ⟨⟨k - i, isComp_rotWord lam hcomp hiw hwrap⟩, ?_⟩
  intro j hj0 hjstart hconn
  obtain ⟨p, hpstart, hpi, hvp⟩ :=
    exists_isCompStart_of_rotWord D lam v hlet hclosed hcomp hjstart hj0
  -- the connection transfers to `w`, where isolatedness forbids it
  have hmem : (vertex (vertex v w i) (rotWord w i) 0)⁻¹ *
      vertex (vertex v w i) (rotWord w i) j ∈ D.fam lam := hconn
  rw [vertex_rotWord_le v w hiw 0 (Nat.zero_le _), hvp, Nat.add_zero] at hmem
  exact hiso.2 p hpi hpstart hmem

end OsinComponents
end GGT
end GroupApproximation
