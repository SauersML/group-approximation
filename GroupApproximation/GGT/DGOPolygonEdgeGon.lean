import GroupApproximation.GGT.DGOIsolatedComponentVertexDist
import GroupApproximation.GGT.DGOReversedSplice
import GroupApproximation.GGT.OsinTheorem54SepSegmentComp
import GroupApproximation.GGT.OsinTheorem54SepSubGeodesic
import GroupApproximation.GGT.OsinTheorem54SepPolygon
import GroupApproximation.GGT.OsinTheorem54SepRuns
import GroupApproximation.GGT.OsinTheorem54SepFinite

/-!
# The edge 4-gon of a cut

In Case B of Dahmani--Guirardel--Osin's Lemma 4.17 the distinguished component
`p₀` is split as `ℓ̂(p₀) ≤ ℓ̂(s) + ℓ̂(e)`, where `s` is the chord component it is
connected to and `e` is the `H_λ`-edge joining `x₁` to `s₋`.  The far polygon
(`DGOPolygonFarGon`) bounds `ℓ̂(s)`; this module builds the 4-gon that bounds
`ℓ̂(e)`:

`comp lam z :: ((w.drop i).take (m - i) ++ q.take t)`,   `z = s₋⁻¹ · x₁`,

read from `s₋`.  Its sides are the edge `e`, the two sides `p₁` and `p₂` of the
original polygon, and the part of the chord from `x₃` back to `s₋`.  It is a
4-gon whatever `n` is --- which is why the recursion `s(n) ≤ n(s(n-1) + s(4))`
has a `s(4)` in it and not a second `s(n-1)`.

## Why the edge is a maximal component

The letter after the edge is `w[c 1]`, and the distinguished component of `w`
*ends* at `c 1`, so its own maximality clause says that letter is not a
`lam`-letter.  Nothing else is needed: unlike the far polygon, the edge 4-gon
has no degenerate case.

## Why it is isolated

A component start on the `w`-block is a component start of `w` --- for index `1`
that fails outright, the letter before it being the edge itself, a `lam`-letter
--- and it is connected to the distinguished component through `s₋`, which
isolation in `w` forbids.  A component start on the chord block has its initial
vertex one letter from `s₋`, so the geodesic `q` puts it at index `t - 1`, and
the chord component's own maximality says the letter there is not a
`lam`-letter.

Concept grep before writing: `(w.drop i).take` across the tree.  The segment
calculus --- `length_segment`, `vertex_segment`, `getElem_segment'`,
`listVal_segment_eq` --- already exists and is used here rather than rebuilt.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The edge word -/

/-- **An `H_λ`-edge, a segment of `w`, and a prefix of the chord.**  Read from
`s₋` this is the 4-gon `e p₁ p₂ (chord prefix)`. -/
def edgeWord (a : RelLetter G Λ) (w : List (RelLetter G Λ)) (i m : ℕ)
    (q : List (RelLetter G Λ)) (t : ℕ) : List (RelLetter G Λ) :=
  (a :: (w.drop i).take (m - i)) ++ q.take t

omit [Group G] in
/-- The edge word has `1 + (m - i) + t` letters. -/
theorem length_edgeWord (a : RelLetter G Λ) (w : List (RelLetter G Λ)) {i m : ℕ}
    (q : List (RelLetter G Λ)) {t : ℕ} (him : i ≤ m) (hm : m ≤ w.length)
    (ht : t ≤ q.length) :
    (edgeWord a w i m q t).length = 1 + (m - i) + t := by
  show ((a :: (w.drop i).take (m - i)) ++ q.take t).length = 1 + (m - i) + t
  rw [List.length_append, List.length_cons,
    length_segment w i (m - i) (by omega), List.length_take_of_le ht]
  omega

/-- Its letters are the edge, letters of `w`, and letters of `q`. -/
theorem letters_edgeWord (D : RelGenSet G Λ) {a : RelLetter G Λ}
    (ha : D.IsLetter a) {w q : List (RelLetter G Λ)}
    (hlet : ∀ b ∈ w, D.IsLetter b) (hq : ∀ b ∈ q, D.IsLetter b) (i m t : ℕ) :
    ∀ b ∈ edgeWord a w i m q t, D.IsLetter b := by
  intro b hb
  have hb' : b ∈ (a :: (w.drop i).take (m - i)) ++ q.take t := hb
  rcases List.mem_append.mp hb' with h | h
  · rcases List.mem_cons.mp h with rfl | h'
    · exact ha
    · exact hlet b (List.drop_subset i w (List.take_subset (m - i) (w.drop i) h'))
  · exact hq b (List.take_subset t q h)

/-- **The edge word is closed**: the edge runs from `s₋` to `vertex v w i`, the
segment from there to `vertex v w m`, and the chord prefix back to `s₋`. -/
theorem listVal_edgeWord_eq_one (v x : G) {a : RelLetter G Λ}
    {w q : List (RelLetter G Λ)} {i m t : ℕ} (him : i ≤ m)
    (ha : a.val = x⁻¹ * vertex v w i)
    (hx : vertex (vertex v w m) q t = x) :
    RelLetter.listVal (edgeWord a w i m q t) = 1 := by
  show RelLetter.listVal ((a :: (w.drop i).take (m - i)) ++ q.take t) = 1
  have hxx : vertex v w m * RelLetter.listVal (q.take t) = x := by
    rw [← vertex_eq_mul_listVal_take q (vertex v w m) t]
    exact hx
  rw [listVal_append, listVal_cons, ha, listVal_segment_eq v w him,
    show x⁻¹ * vertex v w i * ((vertex v w i)⁻¹ * vertex v w m) *
        RelLetter.listVal (q.take t)
      = x⁻¹ * (vertex v w m * RelLetter.listVal (q.take t)) from by group,
    hxx, inv_mul_cancel]

/-! ## Its vertices -/

/-- On the `w`-block, the vertices are those of `w`, shifted by `i`. -/
theorem vertex_edgeWord_seg (v x : G) {a : RelLetter G Λ}
    {w q : List (RelLetter G Λ)} {i m t : ℕ} (him : i ≤ m) (hm : m ≤ w.length)
    (ha : a.val = x⁻¹ * vertex v w i) (p j k : ℕ) (hpj : p = j + 1)
    (hk : k = i + j) (hj : j ≤ m - i) :
    vertex x (edgeWord a w i m q t) p = vertex v w k := by
  show vertex x ((a :: (w.drop i).take (m - i)) ++ q.take t) p = vertex v w k
  rw [vertex_append_of_le (a :: (w.drop i).take (m - i)) (q.take t) x p
      (by rw [List.length_cons, length_segment w i (m - i) (by omega)]; omega),
    hpj, vertex_cons_succ, ha,
    show x * (x⁻¹ * vertex v w i) = vertex v w i from by group, hk]
  exact vertex_segment w v i (m - i) j hj

/-- On the chord block, the vertices are those of `q`, read from
`vertex v w m`. -/
theorem vertex_edgeWord_chord (v x : G) {a : RelLetter G Λ}
    {w q : List (RelLetter G Λ)} {i m t : ℕ} (him : i ≤ m) (hm : m ≤ w.length)
    (ha : a.val = x⁻¹ * vertex v w i) (p j : ℕ) (hpj : p = 1 + (m - i) + j)
    (hj : j ≤ t) :
    vertex x (edgeWord a w i m q t) p = vertex (vertex v w m) q j := by
  show vertex x ((a :: (w.drop i).take (m - i)) ++ q.take t) p = _
  rw [show p = (a :: (w.drop i).take (m - i)).length + j from by
      rw [List.length_cons, length_segment w i (m - i) (by omega)]; omega,
    vertex_append_add (a :: (w.drop i).take (m - i)) (q.take t) x j,
    listVal_cons, ha, listVal_segment_eq v w him,
    show x * (x⁻¹ * vertex v w i * ((vertex v w i)⁻¹ * vertex v w m))
      = vertex v w m from by group]
  exact vertex_take_eq (vertex v w m) q t j hj

/-! ## Its letters -/

omit [Group G] in
/-- The first letter is the edge. -/
theorem getElem_edgeWord_zero {a : RelLetter G Λ} {w q : List (RelLetter G Λ)}
    {i m t : ℕ} (h0 : 0 < (edgeWord a w i m q t).length) :
    (edgeWord a w i m q t)[0]'h0 = a := by
  have h1 : (edgeWord a w i m q t)[0]? = some a := by
    show ((a :: (w.drop i).take (m - i)) ++ q.take t)[0]? = some a
    rw [List.cons_append]
    exact List.getElem?_cons_zero
  rw [List.getElem?_eq_getElem h0] at h1
  exact Option.some.inj h1

omit [Group G] in
/-- On the `w`-block, the letters are those of `w`. -/
theorem getElem_edgeWord_seg {a : RelLetter G Λ} {w q : List (RelLetter G Λ)}
    {i m t p j k : ℕ} (hpj : p = j + 1) (hk : k = i + j) (hj : j < m - i)
    (hm : m ≤ w.length) (hp : p < (edgeWord a w i m q t).length)
    (hkw : k < w.length) :
    (edgeWord a w i m q t)[p]'hp = w[k]'hkw := by
  have hseg : j < ((w.drop i).take (m - i)).length := by
    rw [length_segment w i (m - i) (by omega)]
    exact hj
  have h1 : (edgeWord a w i m q t)[p]? = ((w.drop i).take (m - i))[j]? := by
    show ((a :: (w.drop i).take (m - i)) ++ q.take t)[p]? = _
    rw [List.getElem?_append_left
        (by rw [List.length_cons]; omega), hpj]
    exact List.getElem?_cons_succ
  rw [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hseg] at h1
  rw [Option.some.inj h1, ← getElem_segment' w i (m - i) j k hseg hkw hk]

omit [Group G] in
/-- On the chord block, the letters are those of `q`. -/
theorem getElem_edgeWord_chord {a : RelLetter G Λ} {w q : List (RelLetter G Λ)}
    {i m t p j : ℕ} (hpj : p = 1 + (m - i) + j) (him : i ≤ m) (hm : m ≤ w.length)
    (hj : j < t) (ht : t ≤ q.length)
    (hp : p < (edgeWord a w i m q t).length) (hjq : j < q.length) :
    (edgeWord a w i m q t)[p]'hp = q[j]'hjq := by
  have hlen1 : (a :: (w.drop i).take (m - i)).length = 1 + (m - i) := by
    rw [List.length_cons, length_segment w i (m - i) (by omega)]
    omega
  have htk : j < (q.take t).length := by
    rw [List.length_take_of_le ht]
    exact hj
  have h1 : (edgeWord a w i m q t)[p]? = q[j]? := by
    show ((a :: (w.drop i).take (m - i)) ++ q.take t)[p]? = _
    rw [List.getElem?_append_right (by omega), hlen1,
      show p - (1 + (m - i)) = j from by omega, List.getElem?_take_of_lt hj]
  rw [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hjq] at h1
  exact Option.some.inj h1

/-! ## Component starts on the `w`-block -/

omit [Group G] in
/-- **A component start of the edge word on the `w`-block, past its first
letter, is a component start of `w`.** -/
theorem isCompStart_of_edgeWord_seg (lam : Λ) {a : RelLetter G Λ}
    {w q : List (RelLetter G Λ)} {i m t p j : ℕ} (hpj : p = j + 1) (hj0 : 0 < j)
    (hj : j < m - i) (hm : m ≤ w.length) (hiw : i + j < w.length)
    (hstart : IsCompStart lam (edgeWord a w i m q t) p) :
    IsCompStart lam w (i + j) := by
  obtain ⟨k, hpk, hkE, hrange, hprev, -⟩ := hstart
  have hplen : p < (edgeWord a w i m q t).length := lt_of_lt_of_le hpk hkE
  have hcp : ((edgeWord a w i m q t)[p]'hplen).IsCompOf lam :=
    hrange p le_rfl hpk hplen
  rw [getElem_edgeWord_seg hpj rfl hj hm hplen hiw] at hcp
  obtain ⟨i₀, k₀, hi₀, hk₀, hcomp₀⟩ :=
    exists_isComp_of_isCompOf lam w (i + j) hiw hcp
  refine ⟨k₀, ?_⟩
  have hi₀eq : i₀ = i + j := by
    by_contra hne
    have hpm1 : p - 1 < (edgeWord a w i m q t).length := by omega
    have hprevw := hcomp₀.2.2.1 (i + (j - 1)) (by omega) (by omega) (by omega)
    have hprevE := hprev (p - 1) (by omega) hpm1
    rw [getElem_edgeWord_seg (j := j - 1) (k := i + (j - 1)) (by omega) rfl
      (by omega) hm hpm1 (by omega)] at hprevE
    exact hprevE hprevw
  rw [← hi₀eq]
  exact hcomp₀

/-! ## The edge 4-gon -/

/-- **Dahmani--Guirardel--Osin, Lemma 4.17, the edge of the split.**

`s₋` is the initial vertex of the chord component --- the chord's last letter,
by the `s₊` argument --- and it lies in the coset of `v`.  The edge from `x₁` to
`s₋` is then an `H_λ`-edge, and it is an isolated component of the 4-gon
`e p₁ p₂ (chord prefix)`.  The 4-gon bound applies, with no dependence on `n`.

The conclusion is the second factor of the Case B split: together with the far
polygon's `v⁻¹ · s₋` it multiplies to `(vertex v w (c 0))⁻¹ · vertex v w (c 1)`,
the label of the distinguished component. -/
theorem span_mem_relBall_of_edgeGon (D : RelGenSet G Λ) (C : ℕ)
    (hbase : ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c 4 = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / 1 - 0
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * 4))
    (v : G) {w : List (RelLetter G Λ)} {c : ℕ → ℕ} {n : ℕ}
    {q : List (RelLetter G Λ)} (lam : Λ)
    (hlet : ∀ a ∈ w, D.IsLetter a)
    (hc0 : c 0 = 0) (hcn : c n = w.length) (hcmono : ∀ s : ℕ, c s ≤ c (s + 1))
    (h3n : 3 ≤ n)
    (hcqg : ∀ s : ℕ, s < n → s ≠ 0 → ∀ p q' : ℕ, c s ≤ p → p ≤ q' →
      q' ≤ c (s + 1) → ((q' - p : ℕ) : ℝ) / 1 - 0
        ≤ ((wordDist D.alphabet.carrier (vertex v w p)
            (vertex v w q') : ℕ) : ℝ))
    (hcomp : IsComp lam w (c 0) (c 1)) (hiso : IsIsolated D.fam lam v w (c 0))
    (hq : IsGeodesicWord D (vertex v w (c 3)) v q) (hc13 : c 1 < c 3)
    (hcompq : IsComp lam q (q.length - 1) q.length)
    (hconn : v⁻¹ * vertex (vertex v w (c 3)) q (q.length - 1) ∈ D.fam lam) :
    (vertex (vertex v w (c 3)) q (q.length - 1))⁻¹ * vertex v w (c 1)
      ∈ D.relBall lam (C * 4) := by
  have hmono : Monotone c := monotone_nat_of_le_succ hcmono
  have hc01 : c 0 < c 1 := hcomp.1
  have hc3w : c 3 ≤ w.length := by
    have h := hmono (show 3 ≤ n by omega)
    rw [hcn] at h
    exact h
  set t : ℕ := q.length - 1 with htdef
  have hqpos : 0 < q.length := by
    have h := hcompq.1
    omega
  have htq : t ≤ q.length := by omega
  set x : G := vertex (vertex v w (c 3)) q t with hxdef
  -- the edge is an `H lam`-letter
  have hspan0 : v⁻¹ * vertex v w (c 1) ∈ D.fam lam := by
    have h := span_mem_fam_of_isComp D v hlet hcomp
    rwa [hc0, vertex_zero] at h
  have hz : x⁻¹ * vertex v w (c 1) ∈ D.fam lam := by
    have h := mul_mem (inv_mem hconn) hspan0
    rwa [show (v⁻¹ * x)⁻¹ * (v⁻¹ * vertex v w (c 1))
      = x⁻¹ * vertex v w (c 1) from by group] at h
  set a : RelLetter G Λ := RelLetter.comp lam (x⁻¹ * vertex v w (c 1))
  have haval : a.val = x⁻¹ * vertex v w (c 1) := rfl
  have haLet : D.IsLetter a := hz
  have hacomp : a.IsCompOf lam := rfl
  have hlenE : (edgeWord a w (c 1) (c 3) q t).length = 1 + (c 3 - c 1) + t :=
    length_edgeWord a w q (by omega) hc3w htq
  -- the cut function of the edge 4-gon
  set g : ℕ → ℕ := fun s => if s = 0 then 0 else if s ≤ 3 then 1 + (c s - c 1)
    else 1 + (c 3 - c 1) + t
  have hgv : ∀ s : ℕ, g s = if s = 0 then 0 else if s ≤ 3 then 1 + (c s - c 1)
      else 1 + (c 3 - c 1) + t := fun s => rfl
  have hg0 : g 0 = 0 := by rw [hgv 0, if_pos rfl]
  have hgmid : ∀ s : ℕ, 1 ≤ s → s ≤ 3 → g s = 1 + (c s - c 1) := by
    intro s hs1 hs3
    rw [hgv s, if_neg (by omega), if_pos hs3]
  have hghi : ∀ s : ℕ, 4 ≤ s → g s = 1 + (c 3 - c 1) + t := by
    intro s hs
    rw [hgv s, if_neg (by omega), if_neg (by omega)]
  have hg1 : g 1 = 1 := by
    rw [hgmid 1 (by omega) (by omega)]
    omega
  have hg4 : g 4 = (edgeWord a w (c 1) (c 3) q t).length := by
    rw [hghi 4 (by omega), hlenE]
  have hgmono : ∀ s : ℕ, g s ≤ g (s + 1) := by
    intro s
    rcases Nat.eq_zero_or_pos s with rfl | hs1
    · rw [hg0]
      omega
    · rcases Nat.lt_or_ge s 3 with hs3 | hs3
      · rw [hgmid s (by omega) (by omega), hgmid (s + 1) (by omega) (by omega)]
        have hstep := hcmono s
        have h1s : c 1 ≤ c s := hmono (by omega)
        omega
      · rcases Nat.eq_or_lt_of_le hs3 with hs3' | hs4
        · rw [← hs3', hgmid 3 (by omega) (by omega), hghi (3 + 1) (by omega)]
          omega
        · exact le_of_eq (by rw [hghi s (by omega), hghi (s + 1) (by omega)])
  -- the quasi-geodesic clause
  have hclause : ∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q' : ℕ, g s ≤ p → p ≤ q' →
      q' ≤ g (s + 1) → ((q' - p : ℕ) : ℝ) / 1 - 0
        ≤ ((wordDist D.alphabet.carrier
            (vertex x (edgeWord a w (c 1) (c 3) q t) p)
            (vertex x (edgeWord a w (c 1) (c 3) q t) q') : ℕ) : ℝ) := by
    intro s hs hs0 p q' hp hpq hq'
    rcases Nat.lt_or_ge s 3 with hs3 | hs3
    · -- a side of the original polygon, read at the same vertices
      rw [hgmid s (by omega) (by omega)] at hp
      rw [hgmid (s + 1) (by omega) (by omega)] at hq'
      have h1s : c 1 ≤ c s := hmono (by omega)
      have hss : c s ≤ c (s + 1) := hcmono s
      have hs13 : c (s + 1) ≤ c 3 := hmono (by omega)
      rw [vertex_edgeWord_seg v x (by omega) hc3w haval p (p - 1)
          (c 1 + (p - 1)) (by omega) rfl (by omega),
        vertex_edgeWord_seg v x (by omega) hc3w haval q' (q' - 1)
          (c 1 + (q' - 1)) (by omega) rfl (by omega)]
      have hkey := hcqg s (by omega) hs0 (c 1 + (p - 1)) (c 1 + (q' - 1))
        (by omega) (by omega) (by omega)
      rwa [show c 1 + (q' - 1) - (c 1 + (p - 1)) = q' - p from by omega] at hkey
    · -- the chord prefix, a sub-path of a geodesic word
      have hs3' : s = 3 := by omega
      subst hs3'
      rw [hgmid 3 (by omega) (by omega)] at hp
      rw [hghi (3 + 1) (by omega)] at hq'
      rw [vertex_edgeWord_chord v x (by omega) hc3w haval p
          (p - (1 + (c 3 - c 1))) (by omega) (by omega),
        vertex_edgeWord_chord v x (by omega) hc3w haval q'
          (q' - (1 + (c 3 - c 1))) (by omega) (by omega)]
      have hgeo := sub_le_wordDist_vertex D hq (p - (1 + (c 3 - c 1)))
        (q' - (1 + (c 3 - c 1))) (by omega) (by omega)
      rw [div_one, sub_zero]
      have hcast : (q' - p : ℕ)
          ≤ wordDist D.alphabet.carrier
            (vertex (vertex v w (c 3)) q (p - (1 + (c 3 - c 1))))
            (vertex (vertex v w (c 3)) q (q' - (1 + (c 3 - c 1)))) := by
        rwa [show q' - (1 + (c 3 - c 1)) - (p - (1 + (c 3 - c 1))) = q' - p from by
          omega] at hgeo
      exact_mod_cast hcast
  -- the edge is a component of the 4-gon
  have hcompE : IsComp lam (edgeWord a w (c 1) (c 3) q t) 0 1 := by
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro p _hp0 hp1 hplen
      have hp : p = 0 := by omega
      subst hp
      rw [getElem_edgeWord_zero]
      exact hacomp
    · intro p hp
      exact absurd hp (by omega)
    · intro h1
      rw [getElem_edgeWord_seg (j := 0) (k := c 1) (by omega) (by omega)
        (by omega) hc3w h1 (by omega)]
      exact hcomp.2.2.2.2 (by omega)
  -- and it is isolated
  have hisoE : IsIsolated D.fam lam x (edgeWord a w (c 1) (c 3) q t) 0 := by
    refine ⟨⟨1, hcompE⟩, ?_⟩
    intro j hj0 hjstart hconnj
    obtain ⟨hjlen, hjcomp⟩ := isCompOf_getElem_of_isCompStart hjstart
    have hmem : x⁻¹ * vertex x (edgeWord a w (c 1) (c 3) q t) j ∈ D.fam lam := by
      have h : (vertex x (edgeWord a w (c 1) (c 3) q t) 0)⁻¹ *
          vertex x (edgeWord a w (c 1) (c 3) q t) j ∈ D.fam lam := hconnj
      rwa [vertex_zero] at h
    rcases Nat.lt_or_ge j (1 + (c 3 - c 1)) with hseg | hchord
    · -- on the `w`-block
      rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hj0) with hj1 | hj2
      · -- index `1`: the letter before it is the edge, which is a `lam`-letter
        obtain ⟨_k, _hjk, _hkE, -, hprev, -⟩ := hjstart
        refine hprev 0 (by omega) (by omega) ?_
        rw [getElem_edgeWord_zero]
        exact hacomp
      · have hstartw : IsCompStart lam w (c 1 + (j - 1)) :=
          isCompStart_of_edgeWord_seg lam (j := j - 1) (by omega) (by omega)
            (by omega) hc3w (by omega) hjstart
        refine hiso.2 (c 1 + (j - 1)) (by omega) hstartw ?_
        show (vertex v w (c 0))⁻¹ * vertex v w (c 1 + (j - 1)) ∈ D.fam lam
        rw [hc0, vertex_zero, ← vertex_edgeWord_seg v x (by omega) hc3w haval
          j (j - 1) (c 1 + (j - 1)) (by omega) rfl (by omega)]
        have h := mul_mem hconn hmem
        rwa [show v⁻¹ * x * (x⁻¹ * vertex x (edgeWord a w (c 1) (c 3) q t) j)
          = v⁻¹ * vertex x (edgeWord a w (c 1) (c 3) q t) j from by group] at h
    · -- on the chord block: the geodesic pins the index at `t - 1`
      have hj2 : j - (1 + (c 3 - c 1)) < t := by omega
      rw [vertex_edgeWord_chord v x (by omega) hc3w haval j
        (j - (1 + (c 3 - c 1))) (by omega) (by omega)] at hmem
      have hone := wordDist_le_one_of_mem_fam D hmem
      rw [hxdef] at hone
      have hgeo := sub_le_wordDist_vertex D hq (j - (1 + (c 3 - c 1))) t
        (by omega) htq
      rw [wordDist_comm D.alphabet.symmetricGenerating
        (vertex (vertex v w (c 3)) q (j - (1 + (c 3 - c 1))))
        (vertex (vertex v w (c 3)) q t)] at hgeo
      have hj3 : j = 1 + (c 3 - c 1) + (t - 1) := by omega
      rw [getElem_edgeWord_chord (j := t - 1) hj3 (by omega) hc3w (by omega)
        htq hjlen (by omega)] at hjcomp
      exact hcompq.2.2.2.1 (t - 1) (by omega) (by omega) hjcomp
  have hkey := hbase x (edgeWord a w (c 1) (c 3) q t) g
    (letters_edgeWord D haLet hlet hq.1 (c 1) (c 3) t)
    (listVal_edgeWord_eq_one v x (by omega) haval (by rw [hxdef])) hg0 hg4
    hgmono lam
    hclause (by rw [hg0, hg1]; exact hcompE) (by rw [hg0]; exact hisoE)
  rwa [hg0, hg1, vertex_zero, vertex_edgeWord_seg v x (by omega) hc3w haval
    1 0 (c 1) (by omega) (by omega) (by omega)] at hkey

end OsinComponents
end GGT
end GroupApproximation
