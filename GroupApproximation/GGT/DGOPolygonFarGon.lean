import GroupApproximation.GGT.DGOIsolatedComponentVertexDist
import GroupApproximation.GGT.DGOIsolatedComponentBridge
import GroupApproximation.GGT.DGOReversedSplice
import GroupApproximation.GGT.OsinTheorem54SepCommIndex
import GroupApproximation.GGT.OsinTheorem54SepPolygon

/-!
# The far polygon of a cut, and the component it carries

Dahmani--Guirardel--Osin's Lemma 4.17 cuts an `n`-gon by a geodesic `q` joining
two corners three sides apart.  The *near* side of the cut is the 4-gon built in
`DGOPolygonCutFourGon`; this module builds the *far* side, the `(n-1)`-gon

`revWord q ++ w.drop m`

read from the basepoint `v`.  In their Case B a component `s` of the chord is
connected to the distinguished component, and the bound on the distinguished
component is `ℓ̂(s) + ℓ̂(e)`; the far polygon is where `ℓ̂(s)` comes from, `s`
being an isolated component of it.

## Orientation

The chord is a geodesic word *from* `vertex v w m` *to* `v`, which is the
direction the near 4-gon needs.  The far polygon therefore reverses it, and the
component `s` --- which the `s₊` argument places at the *end* of `q`, of length
one --- becomes the *first* letter of `revWord q`.  So the far polygon presents
it as side `0`, and no rotation is needed: the exempt-side base case applies as
it stands.

Concept grep before writing: `revWord` across the tree.  What exists is the full
index calculus --- `getElem_revWord`, `isComp_revWord`, `vertex_revWord`,
`isGeodesicWord_revWord`, `isLetter_of_mem_revWord` --- and it is used here
rather than rebuilt.  The block lemmas below are the `revWord q ++ w.drop m`
analogues of `DGOPolygonJoin`'s for `w.take m ++ q`.

## Why the component stays maximal

Side `0` is one letter, so the polygon is honest only when the *second* letter
of the far word is not a `lam`-letter.  For `|q| ≥ 2` that is the chord
component's own maximality.  For `|q| = 1` the second letter is `w[m]`, and
`not_isolated_of_span_mem_fam` rules it out: the component of `w` through `m`
would then be connected to the distinguished one and distinct from it, which
isolation forbids.  That lemma is stated for any `m` past `c 1`, and is the only
place isolation in `w` is used before the isolation transfer itself.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The far word -/

/-- **The chord reversed, followed by the tail of `w`.**  Read from `v` this is
the polygon cut off by `q` from the last `|w| - m` letters of `w`. -/
def farWord (q w : List (RelLetter G Λ)) (m : ℕ) : List (RelLetter G Λ) :=
  revWord q ++ w.drop m

/-- The far word has `|q| + (|w| - m)` letters. -/
theorem length_farWord (q w : List (RelLetter G Λ)) (m : ℕ) :
    (farWord q w m).length = q.length + (w.length - m) := by
  show (revWord q ++ w.drop m).length = q.length + (w.length - m)
  rw [List.length_append, length_revWord, List.length_drop]

/-- Its letters are those of `q`, inverted, and those of `w`. -/
theorem letters_farWord (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {q w : List (RelLetter G Λ)}
    (hq : ∀ a ∈ q, D.IsLetter a) (hlet : ∀ a ∈ w, D.IsLetter a) (m : ℕ) :
    ∀ a ∈ farWord q w m, D.IsLetter a := by
  intro a ha
  have ha' : a ∈ revWord q ++ w.drop m := ha
  rcases List.mem_append.mp ha' with h | h
  · exact isLetter_of_mem_revWord D hsymm hq a h
  · exact hlet a (List.drop_subset m w h)

/-- **The far word is closed** when `w` is and the chord spells the way back:
the reversed chord runs from `v` to `vertex v w m`, and `w.drop m` runs back. -/
theorem listVal_farWord_eq_one (v : G) {q w : List (RelLetter G Λ)} {m : ℕ}
    (hclosed : RelLetter.listVal w = 1)
    (hq : RelLetter.listVal q = (vertex v w m)⁻¹ * v) :
    RelLetter.listVal (farWord q w m) = 1 := by
  show RelLetter.listVal (revWord q ++ w.drop m) = 1
  rw [listVal_append, listVal_revWord, hq, listVal_drop_of_closed v hclosed m]
  group

/-! ## Its vertices -/

/-- On the chord block, the vertices are those of the reversed chord. -/
theorem vertex_farWord_le (v : G) {q w : List (RelLetter G Λ)} {m : ℕ}
    (p : ℕ) (hp : p ≤ q.length) :
    vertex v (farWord q w m) p = vertex v (revWord q) p := by
  show vertex v (revWord q ++ w.drop m) p = vertex v (revWord q) p
  exact vertex_append_of_le (revWord q) (w.drop m) v p
    (by rw [length_revWord]; exact hp)

/-- On the chord block, they are the vertices of `q` in reverse order, read from
`vertex v w m`. -/
theorem vertex_farWord_chord (v : G) {q w : List (RelLetter G Λ)} {m : ℕ}
    (hq : RelLetter.listVal q = (vertex v w m)⁻¹ * v) (p : ℕ) (hp : p ≤ q.length) :
    vertex v (farWord q w m) p = vertex (vertex v w m) q (q.length - p) := by
  rw [vertex_farWord_le v p hp]
  have h := vertex_revWord q v (q.length - p)
  rw [show q.length - (q.length - p) = p from by omega] at h
  rw [h, hq, vertex_eq_mul_vertex_one q (vertex v w m) (q.length - p)]
  group

/-- Past the chord, the vertices are those of `w`. -/
theorem vertex_farWord_add (v : G) {q w : List (RelLetter G Λ)} {m : ℕ}
    (hq : RelLetter.listVal q = (vertex v w m)⁻¹ * v) (p t : ℕ)
    (hpt : p = q.length + t) :
    vertex v (farWord q w m) p = vertex v w (m + t) := by
  show vertex v (revWord q ++ w.drop m) p = vertex v w (m + t)
  rw [show p = (revWord q).length + t from by rw [length_revWord]; omega,
    vertex_append_add (revWord q) (w.drop m) v t, listVal_revWord, hq,
    show v * ((vertex v w m)⁻¹ * v)⁻¹ = vertex v w m from by group,
    vertex_eq_mul_vertex_one (w.drop m) (vertex v w m) t, vertex_drop_eq w v m t]

/-! ## Its letters -/

/-- On the chord block, the letters are the inverted letters of `q`, in reverse
order. -/
theorem getElem_farWord_lt {q w : List (RelLetter G Λ)} {m p : ℕ}
    (hp : p < (farWord q w m).length) (hpq : p < q.length)
    (hidx : q.length - 1 - p < q.length) :
    (farWord q w m)[p]'hp = invLetter (q[q.length - 1 - p]'hidx) := by
  have hprev : p < (revWord q).length := by rw [length_revWord]; exact hpq
  have h1 : (farWord q w m)[p]? = (revWord q)[p]? := by
    show (revWord q ++ w.drop m)[p]? = (revWord q)[p]?
    exact List.getElem?_append_left hprev
  rw [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hprev] at h1
  rw [Option.some.inj h1, getElem_revWord q hprev hidx]

/-- Past the chord, the letters are those of `w`. -/
theorem getElem_farWord_add {q w : List (RelLetter G Λ)} {m p t : ℕ}
    (hpt : p = q.length + t) (hp : p < (farWord q w m).length)
    (hmt : m + t < w.length) :
    (farWord q w m)[p]'hp = w[m + t]'hmt := by
  have h1 : (farWord q w m)[p]? = w[m + t]? := by
    show (revWord q ++ w.drop m)[p]? = w[m + t]?
    rw [List.getElem?_append_right (by rw [length_revWord]; omega),
      length_revWord, show p - q.length = t from by omega, List.getElem?_drop]
  rw [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hmt] at h1
  exact Option.some.inj h1

/-! ## What isolation in `w` forbids -/

/-- **A vertex of `w` in the coset of the distinguished component carries no
component of `w` at all**, once it is past the end of that component.

If a component of `w` runs through `m` then its initial vertex lies in the coset
of `vertex v w m`, which is the coset of `v`; so that component is connected to
the distinguished one.  It is not the distinguished one, whose end
`isComp_end_unique` pins at `c 1 < m`.  Isolation forbids the pair. -/
theorem not_isolated_of_span_mem_fam (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {c : ℕ → ℕ}
    (hc0 : c 0 = 0) (hcomp : IsComp lam w (c 0) (c 1))
    (hiso : IsIsolated D.fam lam v w (c 0)) {m : ℕ} (hc1m : c 1 < m)
    (hmem : v⁻¹ * vertex v w m ∈ D.fam lam) {i₀ k₀ : ℕ}
    (hcomp₀ : IsComp lam w i₀ k₀) (hi₀ : i₀ ≤ m) (hk₀ : m ≤ k₀) : False := by
  have hspan := span_mem_fam_of_mem_comp D lam v hlet hcomp₀ hi₀ hk₀
  have hne : i₀ ≠ c 0 := by
    intro hEq
    subst hEq
    have hkk := isComp_end_unique hcomp₀ hcomp
    omega
  refine hiso.2 i₀ hne ⟨k₀, hcomp₀⟩ ?_
  show (vertex v w (c 0))⁻¹ * vertex v w i₀ ∈ D.fam lam
  rw [hc0, vertex_zero]
  have h := mul_mem hmem (inv_mem hspan)
  rwa [show v⁻¹ * vertex v w m * ((vertex v w i₀)⁻¹ * vertex v w m)⁻¹
    = v⁻¹ * vertex v w i₀ from by group] at h

/-- **The second letter of the far word is not a `lam`-letter.**

For `|q| ≥ 2` it is the chord's letter before its last component, which that
component's maximality excludes.  For `|q| = 1` it is `w[m]`, and then the
component's start vertex is `vertex v w m` itself, so
`not_isolated_of_span_mem_fam` applies. -/
theorem not_isCompOf_farWord_one (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w q : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {c : ℕ → ℕ}
    (hc0 : c 0 = 0) (hcomp : IsComp lam w (c 0) (c 1))
    (hiso : IsIsolated D.fam lam v w (c 0)) (hc13 : c 1 < c 3)
    (_hqval : RelLetter.listVal q = (vertex v w (c 3))⁻¹ * v)
    (hcompq : IsComp lam q (q.length - 1) q.length)
    (hconn : v⁻¹ * vertex (vertex v w (c 3)) q (q.length - 1) ∈ D.fam lam)
    (h1 : 1 < (farWord q w (c 3)).length) :
    ¬ ((farWord q w (c 3))[1]'h1).IsCompOf lam := by
  intro hc
  have hqpos : 0 < q.length := by have h := hcompq.1; omega
  have hlenF : (farWord q w (c 3)).length = q.length + (w.length - c 3) :=
    length_farWord q w (c 3)
  rcases Nat.lt_or_ge 1 q.length with hq2 | hq1
  · have hidx : q.length - 1 - 1 < q.length := by omega
    rw [getElem_farWord_lt h1 hq2 hidx, isCompOf_invLetter] at hc
    exact hcompq.2.2.2.1 (q.length - 1 - 1) (by omega) hidx hc
  · have hq1' : q.length = 1 := by omega
    have hmt : c 3 + 0 < w.length := by omega
    rw [getElem_farWord_add (t := 0) (by omega) h1 hmt] at hc
    obtain ⟨i₀, k₀, hi₀, hk₀, hcomp₀⟩ :=
      exists_isComp_of_isCompOf lam w (c 3 + 0) hmt hc
    refine not_isolated_of_span_mem_fam D lam v hlet hc0 hcomp hiso
      (m := c 3) hc13 ?_ hcomp₀ (by omega) (by omega)
    have hz : q.length - 1 = 0 := by omega
    rwa [hz, vertex_zero] at hconn

/-! ## Component starts past the chord -/

/-- **A component start of the far word strictly past the chord is a component
start of `w`.**  Its letter and the letter before it are both letters of `w`, so
the run of `w` through it starts where the run of the far word does. -/
theorem isCompStart_of_farWord_add (lam : Λ) {q w : List (RelLetter G Λ)}
    {m j t : ℕ} (hjt : j = q.length + t) (ht : 0 < t)
    (hjstart : IsCompStart lam (farWord q w m) j) (hmt : m + t < w.length) :
    IsCompStart lam w (m + t) := by
  obtain ⟨k, hjk, hkF, hrange, hprev, -⟩ := hjstart
  have hjlen : j < (farWord q w m).length := lt_of_lt_of_le hjk hkF
  have hcj : ((farWord q w m)[j]'hjlen).IsCompOf lam := hrange j le_rfl hjk hjlen
  rw [getElem_farWord_add hjt hjlen hmt] at hcj
  obtain ⟨i₀, k₀, hi₀, hk₀, hcomp₀⟩ := exists_isComp_of_isCompOf lam w (m + t) hmt hcj
  refine ⟨k₀, ?_⟩
  have hi₀eq : i₀ = m + t := by
    by_contra hne
    have hjm1 : j - 1 < (farWord q w m).length := by omega
    have hprevw := hcomp₀.2.2.1 (m + (t - 1)) (by omega) (by omega) (by omega)
    have hprevF := hprev (j - 1) (by omega) hjm1
    rw [getElem_farWord_add (t := t - 1) (by omega) hjm1 (by omega)] at hprevF
    exact hprevF hprevw
  rw [← hi₀eq]
  exact hcomp₀

/-! ## The far polygon -/

/-- **Dahmani--Guirardel--Osin, Lemma 4.17, the far side of the cut.**

Given the distinguished component `[c 0, c 1)` of an `n`-gon, a geodesic chord
`q` from `vertex v w (c 3)` back to `v`, and the Case B data --- the chord's last
letter is a component of `q`, and its initial vertex lies in the coset of `v` ---
the far word is an `N`-gon, `N = n - 1`, whose side `0` is that letter and is an
isolated component of it.  The `N`-gon bound therefore bounds the chord
component's label.

The sides are: the chord's last letter; the rest of the reversed chord, which is
geodesic; and the sides `p₃, …, p_{n-1}` of the original polygon, read at the
same vertices.

Isolation is a three-way split.  A component start on the chord block is pinned
to index `≤ 1` by the geodesic --- its initial vertex is one letter from `v` ---
and index `1` is excluded by `not_isCompOf_farWord_one`.  A component start past
the chord is a component start of `w`, connected to the distinguished component,
which isolation in `w` forbids. -/
theorem span_mem_relBall_of_farGon (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (mu b : ℝ) (hmu : 1 ≤ mu)
    (hb : 0 ≤ b) (C : ℕ) {N : ℕ}
    (hprev : ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ),
      (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → c 0 = 0 →
      c N = w.length → (∀ s : ℕ, c s ≤ c (s + 1)) → ∀ lam : Λ,
      (∀ s : ℕ, s < N → s ≠ 0 → ∀ p q : ℕ, c s ≤ p → p ≤ q →
        q ≤ c (s + 1) → ((q - p : ℕ) : ℝ) / mu - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p)
              (vertex v w q) : ℕ) : ℝ)) →
      IsComp lam w (c 0) (c 1) → IsIsolated D.fam lam v w (c 0) →
        (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * N))
    (v : G) {w : List (RelLetter G Λ)} {c : ℕ → ℕ} {n : ℕ}
    {q : List (RelLetter G Λ)} (lam : Λ)
    (hlet : ∀ a ∈ w, D.IsLetter a) (hclosed : RelLetter.listVal w = 1)
    (hc0 : c 0 = 0) (hcn : c n = w.length) (hcmono : ∀ s : ℕ, c s ≤ c (s + 1))
    (hnN : n = N + 1) (h3N : 3 ≤ N)
    (hcqg : ∀ s : ℕ, s < n → s ≠ 0 → ∀ p q' : ℕ, c s ≤ p → p ≤ q' →
      q' ≤ c (s + 1) → ((q' - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p)
            (vertex v w q') : ℕ) : ℝ))
    (hcomp : IsComp lam w (c 0) (c 1)) (hiso : IsIsolated D.fam lam v w (c 0))
    (hq : IsGeodesicWord D (vertex v w (c 3)) v q) (hc13 : c 1 < c 3)
    (hcompq : IsComp lam q (q.length - 1) q.length)
    (hconn : v⁻¹ * vertex (vertex v w (c 3)) q (q.length - 1) ∈ D.fam lam) :
    v⁻¹ * vertex (vertex v w (c 3)) q (q.length - 1) ∈ D.relBall lam (C * N) := by
  have hmono : Monotone c := monotone_nat_of_le_succ hcmono
  have hc3w : c 3 ≤ w.length := by
    have h := hmono (show 3 ≤ n by omega)
    rw [hcn] at h
    exact h
  have hqval : RelLetter.listVal q = (vertex v w (c 3))⁻¹ * v :=
    eq_inv_mul_of_mul_eq hq.2.1
  have hqpos : 0 < q.length := by have h := hcompq.1; omega
  have hlenF : (farWord q w (c 3)).length = q.length + (w.length - c 3) :=
    length_farWord q w (c 3)
  have hrev : IsGeodesicWord D v (vertex v w (c 3)) (revWord q) :=
    isGeodesicWord_revWord D hsymm hq
  -- the cut function of the far polygon
  set e : ℕ → ℕ := fun s => if s = 0 then 0 else if s = 1 then 1
    else q.length + (c (s + 1) - c 3)
  have hev : ∀ s : ℕ, e s = if s = 0 then 0 else if s = 1 then 1
      else q.length + (c (s + 1) - c 3) := fun s => rfl
  have he0 : e 0 = 0 := by rw [hev 0, if_pos rfl]
  have he1 : e 1 = 1 := by rw [hev 1, if_neg (by omega), if_pos rfl]
  have hege : ∀ s : ℕ, 2 ≤ s → e s = q.length + (c (s + 1) - c 3) := by
    intro s hs
    rw [hev s, if_neg (by omega), if_neg (by omega)]
  have he2 : e (1 + 1) = q.length := by
    rw [hev (1 + 1), if_neg (by omega), if_neg (by omega),
      show (1 : ℕ) + 1 + 1 = 3 from by norm_num]
    omega
  have heN : e N = (farWord q w (c 3)).length := by
    rw [hege N (by omega), hlenF, show N + 1 = n from hnN.symm, hcn]
  have hemono : ∀ s : ℕ, e s ≤ e (s + 1) := by
    intro s
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · rw [he0]
      omega
    · rcases Nat.eq_or_lt_of_le hs with h1 | h2
      · rw [← h1, he1, he2]
        omega
      · rw [hege s (by omega), hege (s + 1) (by omega)]
        have hstep := hcmono (s + 1)
        omega
  -- the quasi-geodesic clause
  have hclause : ∀ s : ℕ, s < N → s ≠ 0 → ∀ p q' : ℕ, e s ≤ p → p ≤ q' →
      q' ≤ e (s + 1) → ((q' - p : ℕ) : ℝ) / mu - b
        ≤ ((wordDist D.alphabet.carrier (vertex v (farWord q w (c 3)) p)
            (vertex v (farWord q w (c 3)) q') : ℕ) : ℝ) := by
    intro s hs hs0 p q' hp hpq hq'
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hs0) with h1 | h2
    · -- the tail of the reversed chord: a sub-path of a geodesic word
      rw [← h1, he1] at hp
      rw [← h1, he2] at hq'
      have hgeo := sub_le_wordDist_vertex D hrev p q' hpq
        (by rw [length_revWord]; omega)
      rw [← vertex_farWord_le (q := q) (w := w) (m := c 3) v p (by omega),
        ← vertex_farWord_le (q := q) (w := w) (m := c 3) v q' (by omega)] at hgeo
      exact le_trans (sub_le_self _ hb)
        (le_trans (div_le_self (Nat.cast_nonneg _) hmu)
          (by exact_mod_cast hgeo))
    · -- a side of the original polygon, read at the same vertices
      rw [hege s (by omega)] at hp
      rw [hege (s + 1) (by omega)] at hq'
      have hc3s : c 3 ≤ c (s + 1) := hmono (by omega)
      have hc3s2 : c 3 ≤ c (s + 1 + 1) := hmono (by omega)
      rw [vertex_farWord_add v hqval p (p - q.length) (by omega),
        vertex_farWord_add v hqval q' (q' - q.length) (by omega)]
      have hkey := hcqg (s + 1) (by omega) (by omega) (c 3 + (p - q.length))
        (c 3 + (q' - q.length)) (by omega) (by omega) (by omega)
      rwa [show c 3 + (q' - q.length) - (c 3 + (p - q.length)) = q' - p from by
        omega] at hkey
  -- side `0` is a component of the far polygon
  have hcompF : IsComp lam (farWord q w (c 3)) 0 1 := by
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro p _hp0 hp1 hplen
      have hp : p = 0 := by omega
      subst hp
      have hidx : q.length - 1 - 0 < q.length := by omega
      rw [getElem_farWord_lt hplen (by omega) hidx, isCompOf_invLetter]
      exact hcompq.2.2.1 (q.length - 1 - 0) (by omega) (by omega) hidx
    · intro p hp
      exact absurd hp (by omega)
    · intro h1
      exact not_isCompOf_farWord_one D lam v hlet hc0 hcomp hiso hc13 hqval
        hcompq hconn h1
  -- and it is isolated
  have hisoF : IsIsolated D.fam lam v (farWord q w (c 3)) 0 := by
    refine ⟨⟨1, hcompF⟩, ?_⟩
    intro j hj0 hjstart hconnj
    obtain ⟨hjlen, hjcomp⟩ := isCompOf_getElem_of_isCompStart hjstart
    have hmem : v⁻¹ * vertex v (farWord q w (c 3)) j ∈ D.fam lam := by
      have h : (vertex v (farWord q w (c 3)) 0)⁻¹ *
          vertex v (farWord q w (c 3)) j ∈ D.fam lam := hconnj
      rwa [vertex_zero] at h
    rcases Nat.lt_or_ge q.length j with hgt | hle
    · -- past the chord: a component start of `w`, connected to the
      -- distinguished component
      have hjt : j = q.length + (j - q.length) := by omega
      have hct : c 3 + (j - q.length) < w.length := by omega
      have hstartw : IsCompStart lam w (c 3 + (j - q.length)) :=
        isCompStart_of_farWord_add lam hjt (by omega) hjstart hct
      refine hiso.2 (c 3 + (j - q.length)) (by omega) hstartw ?_
      show (vertex v w (c 0))⁻¹ * vertex v w (c 3 + (j - q.length)) ∈ D.fam lam
      rw [hc0, vertex_zero, ← vertex_farWord_add v hqval j (j - q.length) hjt]
      exact hmem
    · -- on the chord: the geodesic pins the index at `1`, which is not a
      -- component start
      have hgeo := sub_le_wordDist_vertex D hrev 0 j (by omega)
        (by rw [length_revWord]; exact hle)
      rw [vertex_zero,
        ← vertex_farWord_le (q := q) (w := w) (m := c 3) v j hle] at hgeo
      have hone := wordDist_le_one_of_mem_fam D hmem
      have hj1 : j = 1 := by omega
      subst hj1
      exact not_isCompOf_farWord_one D lam v hlet hc0 hcomp hiso hc13 hqval
        hcompq hconn hjlen hjcomp
  have hkey := hprev v (farWord q w (c 3)) e
    (letters_farWord D hsymm hq.1 hlet (c 3))
    (listVal_farWord_eq_one v hclosed hqval) he0 heN hemono lam hclause
    (by rw [he0, he1]; exact hcompF) (by rw [he0]; exact hisoF)
  rwa [he0, he1, vertex_zero, vertex_farWord_chord v hqval 1 (by omega)] at hkey

end OsinComponents
end GGT
end GroupApproximation
