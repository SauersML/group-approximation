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
/-- **A component survives a rotation at any index at or before its start.**

The rotation at `j ≤ i` sends the component `[i,k)` to `[i-j, k-j)`.  Maximality
at the left end is inherited from `w` when `i > j`, and is vacuous when `i = j`;
at the right end it is inherited unless the component ends at `w.length`, which is
the wrap case `hwrap` excludes. -/
theorem isComp_rotWord_of_le (lam : Λ) {w : List (RelLetter G Λ)} {i k j : ℕ}
    (hcomp : IsComp lam w i k) (hji : j ≤ i) (hjw : j ≤ w.length)
    (hwrap : ∀ h0 : 0 < w.length, k = w.length → ¬ (w[0]'h0).IsCompOf lam) :
    IsComp lam (rotWord w j) (i - j) (k - j) := by
  have hik : i < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have hrange := hcomp.2.2.1
  have hprev := hcomp.2.2.2.1
  have hnext := hcomp.2.2.2.2
  have hlen : (rotWord w j).length = w.length := length_rotWord w hjw
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro p hp1 hp2 hpw
    rw [getElem_rotWord_lt w hjw p (j + p) rfl (by omega) hpw (by omega)]
    exact hrange (j + p) (by omega) (by omega) (by omega)
  · intro p hp hpw hc
    rw [getElem_rotWord_lt w hjw p (j + p) rfl (by omega) hpw (by omega)] at hc
    exact hprev (j + p) (by omega) (by omega) hc
  · intro hk hc
    rcases Nat.lt_or_ge (k - j) (w.length - j) with hlt | hge
    · -- the letter at `k` of `w`, which maximality forbids
      rw [getElem_rotWord_lt w hjw (k - j) k (by omega) hlt hk (by omega)] at hc
      exact hnext (by omega) hc
    · -- past the seam: the letter at `0` of `w`, which isolation forbids
      have hkk : k = w.length := by omega
      rw [getElem_rotWord_add w hjw (k - j) 0 (by omega) (by omega) hk
        (by omega)] at hc
      exact hwrap (by omega) hkk hc

omit [Group G] in
/-- **The component at the rotation point becomes the component at `0`.**  The
case `j = i` of `isComp_rotWord_of_le`. -/
theorem isComp_rotWord (lam : Λ) {w : List (RelLetter G Λ)} {i k : ℕ}
    (hcomp : IsComp lam w i k) (hi : i ≤ w.length)
    (hwrap : ∀ h0 : 0 < w.length, k = w.length → ¬ (w[0]'h0).IsCompOf lam) :
    IsComp lam (rotWord w i) 0 (k - i) := by
  have h := isComp_rotWord_of_le lam hcomp le_rfl hi hwrap
  rwa [Nat.sub_self] at h

/-! ## Isolation -/

/-- **Every component start of the rotated word other than the two special ones
comes from one of `w`, at the same vertex.**

Before the seam the correspondence is `p ↦ j + p`; after it, `p ↦ p - (|w| - j)`.
Two indices are excluded: `p = 0`, whose run in `w` may have started before the
rotation point and so need not begin at `j` (that case is handled directly in
`isIsolated_rotWord_of_le`, where only the coset matters), and `p = i - j`, which
is the distinguished component itself.  The seam is the one place where two
components of `w` merge into one of the rotated word, and the merged component's
start is still a component start of `w`: it is `0`, whose predecessor in `w` does
not exist. -/
theorem exists_isCompStart_of_rotWord_of_le (_D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hclosed : RelLetter.listVal w = 1) {i k j : ℕ}
    (hcomp : IsComp lam w i k) (hji : j ≤ i) {p : ℕ}
    (hpstart : IsCompStart lam (rotWord w j) p) (hp0 : p ≠ 0) (hpi : p ≠ i - j) :
    ∃ q : ℕ, IsCompStart lam w q ∧ q ≠ i ∧
      vertex (vertex v w j) (rotWord w j) p = vertex v w q := by
  have hik : i < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have hjw : j ≤ w.length := by omega
  have hlen : (rotWord w j).length = w.length := length_rotWord w hjw
  obtain ⟨p2, hp2⟩ := hpstart
  have hp12 : p < p2 := hp2.1
  have hp2len : p2 ≤ (rotWord w j).length := hp2.2.1
  have hprange := hp2.2.2.1
  have hpprev := hp2.2.2.2.1
  have hplen : p < (rotWord w j).length := by omega
  have hcp := hprange p le_rfl hp12 hplen
  have hp1len : p - 1 < (rotWord w j).length := by omega
  have hprevn := hpprev (p - 1) (by omega) hp1len
  rcases Nat.lt_or_ge p (w.length - j) with hlt | hge
  · -- before the seam
    rw [getElem_rotWord_lt w hjw p (j + p) rfl hlt hplen (by omega)] at hcp
    refine ⟨j + p, ?_, by omega, vertex_rotWord_le v w hjw p (by omega)⟩
    obtain ⟨i₀, k₀, hi₀le, hjk₀, hcomp₀⟩ :=
      exists_isComp_of_isCompOf lam w (j + p) (by omega) hcp
    have hi₀ : i₀ = j + p := by
      by_contra hne
      have hprevw := hcomp₀.2.2.1 (j + (p - 1)) (by omega) (by omega) (by omega)
      rw [getElem_rotWord_lt w hjw (p - 1) (j + (p - 1)) rfl (by omega) hp1len
        (by omega)] at hprevn
      exact hprevn hprevw
    exact ⟨k₀, by rw [← hi₀]; exact hcomp₀⟩
  · -- at or after the seam
    have hpr : p = w.length - j + (p - (w.length - j)) := by omega
    have hrlt : p - (w.length - j) < j := by omega
    rw [getElem_rotWord_add w hjw p (p - (w.length - j)) hpr hrlt hplen
      (by omega)] at hcp
    refine ⟨p - (w.length - j), ?_, by omega,
      vertex_rotWord_add v w hjw hclosed p (p - (w.length - j)) hpr (by omega)⟩
    obtain ⟨i₀, k₀, hi₀le, hjk₀, hcomp₀⟩ :=
      exists_isComp_of_isCompOf lam w (p - (w.length - j)) (by omega) hcp
    have hi₀ : i₀ = p - (w.length - j) := by
      rcases Nat.eq_zero_or_pos (p - (w.length - j)) with h0 | hpos
      · -- the seam itself: the run starts at `0` of `w`, which has no predecessor
        omega
      · by_contra hne
        have hprevw := hcomp₀.2.2.1 (p - (w.length - j) - 1) (by omega) (by omega)
          (by omega)
        rw [getElem_rotWord_add w hjw (p - 1) (p - (w.length - j) - 1) (by omega)
          (by omega) hp1len (by omega)] at hprevn
        exact hprevn hprevw
    exact ⟨k₀, by rw [← hi₀]; exact hcomp₀⟩

/-- **Every other component start of the rotated word comes from one of `w`, at
the same vertex.**  The case `j = i` of `exists_isCompStart_of_rotWord_of_le`,
where the two excluded indices coincide. -/
theorem exists_isCompStart_of_rotWord (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (_hlet : ∀ a ∈ w, D.IsLetter a)
    (hclosed : RelLetter.listVal w = 1) {i k : ℕ} (hcomp : IsComp lam w i k)
    {j : ℕ} (hjstart : IsCompStart lam (rotWord w i) j) (hj0 : j ≠ 0) :
    ∃ p : ℕ, IsCompStart lam w p ∧ p ≠ i ∧
      vertex (vertex v w i) (rotWord w i) j = vertex v w p :=
  exists_isCompStart_of_rotWord_of_le D lam v hclosed hcomp le_rfl hjstart hj0
    (by omega)

/-- **Rotation at any index at or before the component preserves isolatedness.**

Two cases.  A rotated component start `p ≥ 1` comes from a component start of `w`
at the same vertex, so a connection in the rotated word is one in `w`.  A rotated
component start at `p = 0` is the `w`-run through the rotation point `j`, whose
own start may lie before `j`; there the vertex is not preserved, but the coset is,
and that is all isolatedness needs — the start of that run is `Connected` to `j`
by `span_mem_fam`, so a connection to the distinguished component composes into
one in `w`.  It is `hpi` that keeps that run from being the distinguished one:
`p = 0` with `j = i` would be the excluded index. -/
theorem isIsolated_rotWord_of_le (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hclosed : RelLetter.listVal w = 1) {i k j : ℕ} (hcomp : IsComp lam w i k)
    (hiso : IsIsolated D.fam lam v w i) (hji : j ≤ i) (hjw : j ≤ w.length)
    (hwrap : ∀ h0 : 0 < w.length, k = w.length → ¬ (w[0]'h0).IsCompOf lam) :
    IsIsolated D.fam lam (vertex v w j) (rotWord w j) (i - j) := by
  have hik : i < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have hlen : (rotWord w j).length = w.length := length_rotWord w hjw
  have hvi : vertex (vertex v w j) (rotWord w j) (i - j) = vertex v w i := by
    rw [vertex_rotWord_le v w hjw (i - j) (by omega),
      show j + (i - j) = i from by omega]
  refine ⟨⟨k - j, isComp_rotWord_of_le lam hcomp hji hjw hwrap⟩, ?_⟩
  intro p hpi hpstart hconn
  have hmem : (vertex (vertex v w j) (rotWord w j) (i - j))⁻¹ *
      vertex (vertex v w j) (rotWord w j) p ∈ D.fam lam := hconn
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · -- the run through the rotation point: the coset is preserved, the vertex is not
    subst hp0
    have hjlt : j < w.length := by omega
    have hv0 : vertex (vertex v w j) (rotWord w j) 0 = vertex v w j := by
      rw [vertex_rotWord_le v w hjw 0 (by omega), Nat.add_zero]
    obtain ⟨p2, hp2⟩ := hpstart
    have hcj : (w[j]'hjlt).IsCompOf lam := by
      have h := hp2.2.2.1 0 le_rfl hp2.1 (by omega)
      rwa [getElem_rotWord_lt w hjw 0 (j + 0) rfl (by omega) (by omega)
        (by omega)] at h
    obtain ⟨i₀, k₀, hi₀le, hjk₀, hcomp₀⟩ :=
      exists_isComp_of_isCompOf lam w j hjlt hcj
    have hconn₀ : (vertex v w i₀)⁻¹ * vertex v w j ∈ D.fam lam :=
      span_mem_fam D lam v hlet j (by omega) i₀ hi₀le
        (fun m hm1 hm2 hm3 => hcomp₀.2.2.1 m hm1 (by omega) hm3)
    rw [hvi, hv0] at hmem
    refine hiso.2 i₀ (by omega) ⟨k₀, hcomp₀⟩ ?_
    have hrw : (vertex v w i)⁻¹ * vertex v w i₀
        = ((vertex v w i)⁻¹ * vertex v w j) *
          ((vertex v w i₀)⁻¹ * vertex v w j)⁻¹ := by
      group
    show (vertex v w i)⁻¹ * vertex v w i₀ ∈ D.fam lam
    rw [hrw]
    exact mul_mem hmem (inv_mem hconn₀)
  · -- every other rotated start comes from one of `w` at the same vertex
    obtain ⟨q, hqstart, hqi, hvq⟩ :=
      exists_isCompStart_of_rotWord_of_le D lam v hclosed hcomp hji hpstart
        (by omega) hpi
    rw [hvi, hvq] at hmem
    exact hiso.2 q hqi hqstart hmem

/-- **Rotation preserves isolatedness of the distinguished component.**  The case
`j = i` of `isIsolated_rotWord_of_le`. -/
theorem isIsolated_rotWord (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hclosed : RelLetter.listVal w = 1) {i k : ℕ} (hcomp : IsComp lam w i k)
    (hiso : IsIsolated D.fam lam v w i)
    (hwrap : ∀ h0 : 0 < w.length, k = w.length → ¬ (w[0]'h0).IsCompOf lam) :
    IsIsolated D.fam lam (vertex v w i) (rotWord w i) 0 := by
  have hik : i < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have h := isIsolated_rotWord_of_le D lam v hlet hclosed hcomp hiso le_rfl
    (by omega) hwrap
  rwa [Nat.sub_self] at h

end OsinComponents
end GGT
end GroupApproximation
