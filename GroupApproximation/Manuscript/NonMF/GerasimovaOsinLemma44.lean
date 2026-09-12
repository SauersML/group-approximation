import GroupApproximation.Manuscript.NonMF.GerasimovaOsinLemma43
import GroupApproximation.GGT.OsinTheorem54SepGeodesicSides
import GroupApproximation.GGT.OsinTheorem54SepFourGonGeneral
import GroupApproximation.GGT.OsinTheorem54SepSubGeodesic
import GroupApproximation.GGT.OsinTheorem54SepFourGonPinning
import GroupApproximation.GGT.DGOIsolatedComponentBridge
import GroupApproximation.GGT.OsinGeodesicWord

/-!
# Gerasimova–Osin, Lemma 4.4

Gerasimova–Osin (arXiv:1910.14524v3), §4:

> **Lemma 4.4.** Let `p` be as above and let `q` be a geodesic in `Γ(G, 𝒜)` connecting
> `p₋` to `p₊`.  Then `q = c₁d₁ … cₙdₙ`, where `dᵢ ≠ 1` and `cᵢ` is an `H`-component of
> `q` connected to `aᵢ` for all `i ∈ {1, …, n}`.  In particular, the path `p` is
> geodesic.

The proof is by induction on `n`.  The first step closes `p q⁻¹` into the quadrilateral
with sides `q⁻¹, a₁, b₁, a₂b₂ ⋯ aₙbₙ`; the inductive step uses the pentagon with sides
`bᵢ, aᵢ₊₁, bᵢ₊₁ ⋯ aₙbₙ, (q')⁻¹, fᵢ`.  In both, Proposition 3.6 and (16) make the deep
`t`-edge non-isolated, Lemma 4.3 excludes a connection inside `p`, so the edge is
connected to a component of `q`.

## Repository form

* Proposition 3.6 is the projection clause of `GGT.OsinComponents.dgoProposition414Uniform`
  at `(μ, c) = (1, 1)`.  At `(1,1)` every single edge and every short side whose endpoints
  differ is quasi-geodesic, so the connecting edge `fᵢ` needs no case split on being
  trivial; the pentagon is realised as the quadrilateral
  `[fᵢ, bᵢ] ++ aᵢ₊₁ ⋯ aₙbₙ ++ [] ++ revWord q'`, whose first side `fᵢ bᵢ` has distinct
  endpoints because `Lab(bᵢ) ∉ H`.
* The decomposition `q = c₁d₁ ⋯ cₙdₙ` is recorded by positions: for every `i` there is a
  component start `j` of `q` with `2i ≤ j`, `j + 2(n - i) ≤ |q|`, connected to `aᵢ₊₁`
  (`GOMatch`).  These two inequalities are `dᵢ ≠ 1` accumulated from both ends, and
  `|q| ≥ 2n` is the case `i = n - 1`.  When `|q| = 2n` they pin `j = 2i`
  (`GOMatch.tight`), which is what Lemma 4.5 reads.
* The standing assumptions of §4 are bundled in `GOSetting`: `H = D.fam ()`
  hyperbolically embedded with symmetric base, `F ⊆ X`, `F ∩ H = ∅` (Lemma 4.2), and
  `t ∈ H` outside the relative ball of radius `50C` ((16), deepened as in
  `GerasimovaOsinLemma43`).

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (Gerasimova–Osin's Proposition 4.1).
Certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace GerasimovaOsinWords

open GroupApproximation.GGT
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric

universe u w

section Sides

variable {G : Type u} [Group G] {Λ : Type w}

/-- A side of a polygon satisfying the `(1,1)`-quasi-geodesic clause, read from `1`. -/
def IsOneOneSide (D : RelGenSet G Λ) (u : List (RelLetter G Λ)) : Prop :=
  ∀ a c : ℕ, a ≤ c → c ≤ u.length →
    c - a ≤ wordDist D.alphabet.carrier (vertex (1 : G) u a) (vertex (1 : G) u c) + 1

theorem isOneOneSide_of_isGeodesicWord {D : RelGenSet G Λ} {u : List (RelLetter G Λ)}
    (hu : IsGeodesicWord D 1 (RelLetter.listVal u) u) : IsOneOneSide D u := by
  intro a c hac hc
  have h := sub_le_wordDist_vertex D hu a c hac hc
  omega

theorem isOneOneSide_of_length_le_one {D : RelGenSet G Λ} {u : List (RelLetter G Λ)}
    (hu : u.length ≤ 1) : IsOneOneSide D u := by
  intro a c hac hc
  omega

/-- A two-letter side whose endpoints differ is `(1,1)`-quasi-geodesic. -/
theorem isOneOneSide_pair {D : RelGenSet G Λ} (a b : RelLetter G Λ)
    (hab : a.val * b.val ≠ 1) : IsOneOneSide D [a, b] := by
  intro i c hic hc
  by_cases h2 : c - i ≤ 1
  · omega
  · have hc' : c ≤ 2 := hc
    have hc2 : c = 2 := by omega
    have hi0 : i = 0 := by omega
    subst hc2
    subst hi0
    have hv : vertex (1 : G) [a, b] 2 = 1 * RelLetter.listVal [a, b] := vertex_length 1 [a, b]
    have hval : RelLetter.listVal [a, b] = a.val * b.val := by
      rw [listVal_cons, listVal_cons, RelLetter.listVal_nil, mul_one]
    have hne : wordDist D.alphabet.carrier (vertex (1 : G) [a, b] 0)
        (vertex (1 : G) [a, b] 2) ≠ 0 := by
      rw [Ne, wordDist_eq_zero_iff D.alphabet.symmetricGenerating, vertex_zero, hv, hval,
        one_mul]
      exact fun h => hab h.symm
    omega

theorem oneOne_side_clause (D : RelGenSet G Λ) (u : List (RelLetter G Λ)) (f : G) {a c : ℕ}
    (hu : IsOneOneSide D u) (hac : a ≤ c) (hc : c ≤ u.length) :
    ((c - a : ℕ) : ℝ) / 1 - 1
      ≤ ((wordDist D.alphabet.carrier (f * vertex (1 : G) u a)
          (f * vertex (1 : G) u c) : ℕ) : ℝ) := by
  rw [wordDist_left_invariant]
  have hnat := hu a c hac hc
  have hcast : ((c - a : ℕ) : ℝ) ≤ ((wordDist D.alphabet.carrier (vertex (1 : G) u a)
      (vertex (1 : G) u c) : ℕ) : ℝ) + 1 := by
    exact_mod_cast hnat
  rw [div_one]
  linarith

/-- The letters of a quadrilateral, from those of its sides. -/
theorem fourGon_letters {D : RelGenSet G Λ} {p q r s : List (RelLetter G Λ)}
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hp : ∀ a ∈ p, D.IsLetter a) (hq : ∀ a ∈ q, D.IsLetter a) (hr : ∀ a ∈ r, D.IsLetter a)
    (hs : ∀ a ∈ s, D.IsLetter a) : ∀ a ∈ p ++ q ++ r ++ revWord s, D.IsLetter a := by
  intro a ha
  simp only [List.mem_append] at ha
  rcases ha with ((ha | ha) | ha) | ha
  · exact hp a ha
  · exact hq a ha
  · exact hr a ha
  · exact isLetter_of_mem_revWord D hsymm hs a ha

/-- **A quadrilateral of `(1,1)`-sides is a `(1,1)`-quasi-geodesic `4`-gon.**  The proof
is that of `isQuasiGeodesicPolygon_fourGon_of_geodesic`, with the `(1,1)` clause. -/
theorem isQuasiGeodesicPolygon_fourGon_of_oneOneSides (D : RelGenSet G Λ)
    (p q r s : List (RelLetter G Λ))
    (hlet : ∀ a ∈ p ++ q ++ r ++ revWord s, D.IsLetter a)
    (hp : IsOneOneSide D p) (hq : IsOneOneSide D q) (hr : IsOneOneSide D r)
    (hs : IsOneOneSide D s)
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r) :
    IsQuasiGeodesicPolygon D 1 1 4 1 (p ++ q ++ r ++ revWord s) := by
  refine isQuasiGeodesicPolygon_fourGon p q r s D hlet hclose ?_
  intro t ht x y hx hxy hy
  by_cases h0 : t = 0
  · subst h0
    have hy' : y ≤ p.length := hy
    rw [vertex_fourGon_first p q r s 1 (by omega), vertex_fourGon_first p q r s 1 hy']
    have h := oneOne_side_clause D p 1 hp hxy hy'
    rw [one_mul, one_mul] at h
    exact h
  · by_cases h1 : t = 1
    · subst h1
      have hx' : p.length ≤ x := hx
      have hy' : y ≤ p.length + q.length := hy
      obtain ⟨x', rfl⟩ : ∃ x', x = p.length + x' := ⟨x - p.length, by omega⟩
      obtain ⟨y', rfl⟩ : ∃ y', y = p.length + y' := ⟨y - p.length, by omega⟩
      rw [vertex_fourGon_side p q r s 1 (by omega : x' ≤ q.length),
        vertex_fourGon_side p q r s 1 (by omega : y' ≤ q.length), one_mul,
        show p.length + y' - (p.length + x') = y' - x' from by omega]
      exact oneOne_side_clause D q (RelLetter.listVal p) hq (by omega) (by omega)
    · by_cases h2 : t = 2
      · subst h2
        have hx' : p.length + q.length ≤ x := hx
        have hy' : y ≤ p.length + q.length + r.length := hy
        obtain ⟨x', rfl⟩ : ∃ x', x = p.length + q.length + x' :=
          ⟨x - (p.length + q.length), by omega⟩
        obtain ⟨y', rfl⟩ : ∃ y', y = p.length + q.length + y' :=
          ⟨y - (p.length + q.length), by omega⟩
        rw [vertex_fourGon_third p q r s 1 (by omega : x' ≤ r.length),
          vertex_fourGon_third p q r s 1 (by omega : y' ≤ r.length), one_mul,
          show p.length + q.length + y' - (p.length + q.length + x')
            = y' - x' from by omega]
        exact oneOne_side_clause D r
          (RelLetter.listVal p * RelLetter.listVal q) hr (by omega) (by omega)
      · have ht3 : t = 3 := by omega
        subst ht3
        have hx' : p.length + q.length + r.length ≤ x := hx
        have hy' : y ≤ p.length + q.length + r.length + s.length := hy
        obtain ⟨a, rfl⟩ : ∃ a, x = p.length + q.length + r.length + a :=
          ⟨x - (p.length + q.length + r.length), by omega⟩
        obtain ⟨c, rfl⟩ : ∃ c, y = p.length + q.length + r.length + c :=
          ⟨y - (p.length + q.length + r.length), by omega⟩
        rw [show p.length + q.length + r.length + a
              = p.length + q.length + r.length + (s.length - (s.length - a))
            from by omega,
          vertex_fourGon_opposite_closed p q r s hclose (s.length - a),
          show p.length + q.length + r.length + c
              = p.length + q.length + r.length + (s.length - (s.length - c))
            from by omega,
          vertex_fourGon_opposite_closed p q r s hclose (s.length - c),
          wordDist_comm D.alphabet.symmetricGenerating,
          show p.length + q.length + r.length + (s.length - (s.length - c))
              - (p.length + q.length + r.length
                + (s.length - (s.length - a)))
            = s.length - a - (s.length - c) from by omega]
        have h := oneOne_side_clause D s 1 hs
          (by omega : s.length - c ≤ s.length - a) (by omega)
        rw [one_mul, one_mul] at h
        exact h

end Sides

section Reads

variable {G : Type u} [Group G] {Λ : Type w}

theorem vertex_succ_of_getElem? {w : List (RelLetter G Λ)} {v : G} {j : ℕ}
    {a : RelLetter G Λ} (h : w[j]? = some a) :
    vertex v w (j + 1) = vertex v w j * a.val := by
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp h
  rw [vertex_succ w v j hj, hget]

theorem mem_of_getElem?_eq_some {α : Type*} {l : List α} {j : ℕ} {a : α}
    (h : l[j]? = some a) : a ∈ l := by
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp h
  rw [← hget]
  exact List.getElem_mem hj

omit [Group G] in
theorem exists_read_of_isCompStart {w : List (RelLetter G Λ)} {lam : Λ} {j : ℕ}
    (h : IsCompStart lam w j) : ∃ g : G, w[j]? = some (RelLetter.comp lam g) := by
  obtain ⟨hn, hc⟩ := isCompOf_getElem_of_isCompStart h
  exact getElem?_comp_of_isCompOf hn hc

theorem exists_comp_of_invLetter_eq_comp {a : RelLetter G Unit} {g : G}
    (h : invLetter a = RelLetter.comp () g) : ∃ g' : G, a = RelLetter.comp () g' := by
  cases a with
  | base x => simp [invLetter] at h
  | comp lam g' => exact ⟨g', rfl⟩

theorem getElem?_fourGon_q' (p q r s : List (RelLetter G Λ)) {i : ℕ} (hi : i < q.length) :
    (p ++ q ++ r ++ revWord s)[p.length + i]? = q[i]? := by
  rw [List.getElem?_append_left (show p.length + i < (p ++ q ++ r).length by
      rw [List.length_append, List.length_append]; omega),
    List.getElem?_append_left (show p.length + i < (p ++ q).length by
      rw [List.length_append]; omega),
    List.getElem?_append_right (show p.length ≤ p.length + i by omega),
    Nat.add_sub_cancel_left]

theorem getElem?_fourGon_r' (p q r s : List (RelLetter G Λ)) {m : ℕ} (hm : m < r.length) :
    (p ++ q ++ r ++ revWord s)[p.length + q.length + m]? = r[m]? := by
  rw [List.getElem?_append_left (show p.length + q.length + m < (p ++ q ++ r).length by
      rw [List.length_append, List.length_append]; omega),
    List.getElem?_append_right (show (p ++ q).length ≤ p.length + q.length + m by
      rw [List.length_append]; omega),
    show p.length + q.length + m - (p ++ q).length = m by rw [List.length_append]; omega]

theorem getElem?_fourGon_s' (p q r s : List (RelLetter G Λ)) {k : ℕ} (hk : k < s.length) :
    (p ++ q ++ r ++ revWord s)[p.length + q.length + r.length + k]?
      = some (invLetter (s[s.length - 1 - k]'(by omega))) := by
  rw [List.getElem?_append_right (show (p ++ q ++ r).length ≤ p.length + q.length + r.length + k
      by rw [List.length_append, List.length_append]; omega),
    show p.length + q.length + r.length + k - (p ++ q ++ r).length = k by
      rw [List.length_append, List.length_append]; omega,
    List.getElem?_eq_getElem (by rw [length_revWord]; exact hk),
    getElem_revWord s _ (by omega)]

omit [Group G] in
omit [Group G] in
/-- A peripheral letter flanked by base letters (or by the ends of the word) is a
single-letter component. -/
theorem isComp_unit_of_reads {w : List (RelLetter G Unit)} {i : ℕ} {g : G}
    (hi : w[i]? = some (RelLetter.comp () g))
    (hprev : i = 0 ∨ ∃ x : G, w[i - 1]? = some (RelLetter.base x))
    (hnext : i + 1 = w.length ∨ ∃ x : G, w[i + 1]? = some (RelLetter.base x)) :
    IsComp () w i (i + 1) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hi
  refine ⟨Nat.lt_succ_self i, hlt, ?_, ?_, ?_⟩
  · intro j hij hji hj
    have hji' : j = i := by omega
    subst hji'
    rw [hget]
    rfl
  · intro j hj hjlen hc
    rcases hprev with h0 | ⟨x, hx⟩
    · omega
    · have hj' : j = i - 1 := by omega
      subst hj'
      obtain ⟨_, hget'⟩ := List.getElem?_eq_some_iff.mp hx
      rw [hget'] at hc
      exact hc
  · intro hk hc
    rcases hnext with h1 | ⟨x, hx⟩
    · omega
    · obtain ⟨_, hget'⟩ := List.getElem?_eq_some_iff.mp hx
      rw [hget'] at hc
      exact hc

/-- A vertex of a geodesic in the coset of its start is at most one step along it. -/
theorem index_le_one_of_mem_coset {D : RelGenSet G Λ} {f g : G} {w : List (RelLetter G Λ)}
    (hw : IsGeodesicWord D f g w) {lam : Λ} {i : ℕ} (hi : i ≤ w.length)
    (hmem : f⁻¹ * vertex f w i ∈ D.fam lam) : i ≤ 1 := by
  have h1 := sub_le_wordDist_vertex D hw 0 i (Nat.zero_le i) hi
  rw [vertex_zero] at h1
  have h2 := wordDist_le_one_of_mem_fam D hmem
  omega

/-- A geodesic word has no two consecutive letters of one subgroup. -/
theorem not_consecutive_comp_of_isGeodesicWord {D : RelGenSet G Λ} {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) {lam : Λ} {j : ℕ} {g₁ g₂ : G}
    (h₁ : w[j]? = some (RelLetter.comp lam g₁))
    (h₂ : w[j + 1]? = some (RelLetter.comp lam g₂)) : False := by
  have hg₁ : g₁ ∈ D.fam lam := hw.1 _ (mem_of_getElem?_eq_some h₁)
  have hg₂ : g₂ ∈ D.fam lam := hw.1 _ (mem_of_getElem?_eq_some h₂)
  have hv₁ := vertex_succ_of_getElem? (v := f) h₁
  have hv₂ := vertex_succ_of_getElem? (v := f) h₂
  have hlen : j + 2 ≤ w.length := by
    have := (List.getElem?_eq_some_iff.mp h₂).1
    omega
  have hmem : (vertex f w j)⁻¹ * vertex f w (j + 2) ∈ D.fam lam := by
    have he : (vertex f w j)⁻¹ * vertex f w (j + 2) = g₁ * g₂ := by
      rw [show j + 2 = j + 1 + 1 from rfl, hv₂, hv₁]
      simp only [RelLetter.val]
      group
    rw [he]
    exact mul_mem hg₁ hg₂
  have h1 := wordDist_le_one_of_mem_fam D hmem
  have h2 := sub_le_wordDist_vertex D hw j (j + 2) (by omega) hlen
  omega

/-- A suffix of a geodesic word is a geodesic word. -/
theorem geodesic_drop {D : RelGenSet G Λ} {f g : G} {w : List (RelLetter G Λ)}
    (hw : IsGeodesicWord D f g w) {k : ℕ} (hk : k ≤ w.length) :
    IsGeodesicWord D (vertex f w k) g (w.drop k) := by
  have h := isGeodesicWord_segment D hw hk le_rfl
  rw [hw.vertex_length_eq] at h
  have htake : (w.drop k).take (w.length - k) = w.drop k :=
    List.take_of_length_le (by simp)
  rwa [htake] at h

theorem vertex_drop' (w : List (RelLetter G Λ)) (v : G) (k j : ℕ) :
    vertex v w (k + j) = vertex (vertex v w k) (w.drop k) j := by
  rw [← vertex_drop_eq w v k j, vertex_eq_mul_vertex_one (w.drop k) (vertex v w k) j]

/-- The vertex of `t f₁ ⋯ t fₙ` after the first two letters. -/
theorem vertex_altWord_cons (v t f : G) (rest : List G) (m : ℕ) :
    vertex v (altWord t (f :: rest)) (2 + m)
      = v * t * f * vertex (1 : G) (altWord t rest) m := by
  have h := vertex_append_add [RelLetter.comp () t, RelLetter.base f] (altWord t rest) v m
  rw [vertex_eq_mul_vertex_one (altWord t rest), listVal_cons, listVal_cons,
    RelLetter.listVal_nil, mul_one] at h
  simp only [RelLetter.val] at h
  rw [← mul_assoc] at h
  exact h

theorem vertex_altWord_two_mul_succ (v t : G) (fs : List G) {i : ℕ} (hi : i < fs.length) :
    vertex v (altWord t fs) (2 * (i + 1)) = vertex v (altWord t fs) (2 * i) * t * fs[i] := by
  have h1 := vertex_succ_of_getElem? (v := v) (getElem?_altWord_two_mul (t := t) hi)
  have hread : (altWord t fs)[2 * i + 1]? = some (RelLetter.base fs[i]) := by
    rw [getElem?_altWord_odd, List.getElem?_eq_getElem hi]
    rfl
  have h2 := vertex_succ_of_getElem? (v := v) hread
  rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, h2, h1]
  rfl

theorem listVal_altWord_cons (t f : G) (rest : List G) :
    RelLetter.listVal (altWord t (f :: rest)) = t * f * RelLetter.listVal (altWord t rest) := by
  rw [altWord_cons, listVal_cons, listVal_cons]
  simp only [RelLetter.val, mul_assoc]

end Reads

section Setting

variable {G : Type u} [Group G]

/-- **The standing assumptions of Gerasimova–Osin §4**, after Lemma 4.2, (15) and (16).
`C` is the constant of Proposition 3.6 (DGO Proposition 4.14 at `(1,1)`, in both its
sum form and its projection form). -/
structure GOSetting (D : RelGenSet G Unit) (F : Set G) (t : G) (C : ℕ) : Prop where
  base_symm : ∀ x ∈ D.base, x⁻¹ ∈ D.base
  C_pos : 0 < C
  sum_bound : DGOUniformSumBound D 1 1 C
  proj : ∀ (n : ℕ) (v : G) (word : List (RelLetter G Unit)),
    IsQuasiGeodesicPolygon D 1 1 n v word →
    ∀ (lam : Unit) (i k : ℕ), IsComp lam word i k → IsIsolated D.fam lam v word i →
      (vertex v word i)⁻¹ * vertex v word k ∈ D.relBall lam (C * n)
  t_mem : t ∈ D.fam ()
  t_deep : t ∉ D.relBall () (50 * C)
  F_base : ∀ f ∈ F, f ∈ D.base
  F_not_fam : ∀ f ∈ F, f ∉ D.fam ()

/-- **The decomposition `q = c₁d₁ ⋯ cₙdₙ` of Lemma 4.4**, for a word `s` read from `1`:
the `i`-th `t`-edge of `t f₁ ⋯ t fₙ` is connected to a component of `s` starting at `j`,
with `2i ≤ j` and `j + 2(n - i) ≤ |s|`. -/
def GOMatch (D : RelGenSet G Unit) (t : G) (fs : List G) (s : List (RelLetter G Unit)) :
    Prop :=
  2 * fs.length ≤ s.length ∧
    ∀ i : ℕ, i < fs.length → ∃ j : ℕ, 2 * i ≤ j ∧ j + 2 * (fs.length - i) ≤ s.length ∧
      (∃ g : G, s[j]? = some (RelLetter.comp () g)) ∧
      (vertex (1 : G) (altWord t fs) (2 * i))⁻¹ * vertex (1 : G) s j ∈ D.fam ()

/-- The inductive state of the proof of Lemma 4.4: `aᵢ` ends at `x`, the matched
component `cᵢ` of `q` ends at `y`, the rest of `p` is `bᵢ aᵢ₊₁ ⋯ aₙ bₙ` with
`Lab(bᵢ) = f`, and `s` is the rest `q'` of `q`. -/
def GOMatchState (D : RelGenSet G Unit) (t x y f : G) (rest : List G)
    (s : List (RelLetter G Unit)) : Prop :=
  1 + 2 * rest.length ≤ s.length ∧
    ∀ k : ℕ, k < rest.length → ∃ j : ℕ, 2 * k + 1 ≤ j ∧ j + 2 * (rest.length - k) ≤ s.length ∧
      (∃ g : G, s[j]? = some (RelLetter.comp () g)) ∧
      (x * f * vertex (1 : G) (altWord t rest) (2 * k))⁻¹ * vertex y s j ∈ D.fam ()

theorem goMatch_nil {D : RelGenSet G Unit} {t : G} (s : List (RelLetter G Unit)) :
    GOMatch D t [] s :=
  ⟨by simp, fun i hi => absurd hi (by simp)⟩

/-- When `|s| = 2n` the decomposition is exact: `cᵢ` sits at position `2i`. -/
theorem GOMatch.tight {D : RelGenSet G Unit} {t : G} {fs : List G}
    {s : List (RelLetter G Unit)} (hm : GOMatch D t fs s) (hlen : s.length = 2 * fs.length)
    {i : ℕ} (hi : i < fs.length) :
    (∃ g : G, s[2 * i]? = some (RelLetter.comp () g)) ∧
      (vertex (1 : G) (altWord t fs) (2 * i))⁻¹ * vertex (1 : G) s (2 * i) ∈ D.fam () := by
  obtain ⟨j, hj1, hj2, hread, hconn⟩ := hm.2 i hi
  have hj : j = 2 * i := by omega
  rw [hj] at hread hconn
  exact ⟨hread, hconn⟩

/-- The last step of Lemma 4.4: `dₙ` is not trivial, as otherwise `Lab(bₙ) ∈ H`. -/
theorem goMatchState_nil {D : RelGenSet G Unit} {F : Set G} {t : G} {C : ℕ}
    (hS : GOSetting D F t C) {x y f : G} (hf : f ∈ F) (hxy : x⁻¹ * y ∈ D.fam ())
    {s : List (RelLetter G Unit)}
    (hs : IsGeodesicWord D y (x * f * RelLetter.listVal (altWord t [])) s) :
    GOMatchState D t x y f [] s := by
  refine ⟨?_, fun k hk => absurd hk (by simp)⟩
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
  rcases Nat.eq_zero_or_pos s.length with h0 | h0
  · exfalso
    have hs0 : s = [] := List.length_eq_zero_iff.mp h0
    have hval := hs.2.1
    rw [hs0, RelLetter.listVal_nil, mul_one, altWord_nil, RelLetter.listVal_nil,
      mul_one] at hval
    apply hS.F_not_fam f hf
    have he : x⁻¹ * y = f := by
      rw [hval]
      group
    rw [← he]
    exact hxy
  · exact h0

/-- "In particular, the path `p` is geodesic", from `|q| ≥ 2n` for every geodesic `q`. -/
theorem isGeodesicWord_altWord_of_match {D : RelGenSet G Unit} {F : Set G} {t : G} {C : ℕ}
    (hS : GOSetting D F t C) {fs : List G} (hfs : ∀ f ∈ fs, f ∈ F)
    (hmatch : ∀ s : List (RelLetter G Unit),
      IsGeodesicWord D 1 (RelLetter.listVal (altWord t fs)) s → 2 * fs.length ≤ s.length) :
    IsGeodesicWord D 1 (RelLetter.listVal (altWord t fs)) (altWord t fs) := by
  obtain ⟨s, hs⟩ := existsGeodesicWord D 1 (RelLetter.listVal (altWord t fs))
  have h1 := hmatch s hs
  have hlet : ∀ a ∈ altWord t fs, D.IsLetter a :=
    isLetter_altWord D hS.t_mem (fun f hf => hS.F_base f (hfs f hf))
  refine ⟨hlet, one_mul _, ?_⟩
  have h2 : wordDist D.alphabet.carrier 1 (RelLetter.listVal (altWord t fs))
      ≤ (altWord t fs).length := by
    have h := wordDist_vertex_le D hlet (Nat.zero_le (altWord t fs).length) le_rfl
    rwa [vertex_zero, vertex_length, one_mul, Nat.sub_zero] at h
  have h3 := hs.2.2
  rw [length_altWord] at h2 ⊢
  omega

end Setting

section FirstStep

variable {G : Type u} [Group G] {D : RelGenSet G Unit} {F : Set G} {t : G} {C : ℕ}

/-- **The first step of Lemma 4.4**: the quadrilateral `q⁻¹, a₁, b₁, a₂b₂ ⋯ aₙbₙ`.
`a₁` is connected to the first edge `c₁` of `q`, and the rest follows from the inductive
state `hR` after `c₁`. -/
theorem goMatch_cons (hS : GOSetting D F t C) {f : G} {rest : List G} (hf : f ∈ F)
    (hrest : ∀ g ∈ rest, g ∈ F)
    (hgeo : IsGeodesicWord D 1 (RelLetter.listVal (altWord t rest)) (altWord t rest))
    (hR : ∀ (x y : G) (s : List (RelLetter G Unit)), x⁻¹ * y ∈ D.fam () →
      IsGeodesicWord D y (x * f * RelLetter.listVal (altWord t rest)) s →
      (∀ g : G, s[0]? ≠ some (RelLetter.comp () g)) → GOMatchState D t x y f rest s)
    {s : List (RelLetter G Unit)}
    (hs : IsGeodesicWord D 1 (RelLetter.listVal (altWord t (f :: rest))) s) :
    GOMatch D t (f :: rest) s := by
  have hfX : f ∈ D.base := hS.F_base f hf
  have hfH : f ∉ D.fam () := hS.F_not_fam f hf
  have hfsX : ∀ g ∈ f :: rest, g ∈ D.base := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hfX
    · exact hS.F_base g (hrest g hg)
  have hfsH : ∀ g ∈ f :: rest, g ∉ D.fam () := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hfH
    · exact hS.F_not_fam g (hrest g hg)
  have hP : RelLetter.listVal s = t * f * RelLetter.listVal (altWord t rest) := by
    have h := hs.2.1
    rw [one_mul, listVal_altWord_cons] at h
    exact h
  have hclose : RelLetter.listVal s = RelLetter.listVal ([] : List (RelLetter G Unit)) *
      RelLetter.listVal [RelLetter.comp () t, RelLetter.base f] *
      RelLetter.listVal (altWord t rest) := by
    rw [hP]
    simp only [listVal_cons, RelLetter.listVal_nil, RelLetter.val, mul_one, one_mul]
  have hlet : ∀ a ∈ ([] : List (RelLetter G Unit)) ++ [RelLetter.comp () t, RelLetter.base f] ++
      altWord t rest ++ revWord s, D.IsLetter a := by
    refine fourGon_letters hS.base_symm (by simp) ?_ hgeo.1 hs.1
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hS.t_mem
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hfX
    simp at ha
  have htf : (RelLetter.comp () t : RelLetter G Unit).val * (RelLetter.base f : RelLetter G Unit).val ≠ 1 := by
    intro h
    apply hfH
    have h' : f = t⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h']
    exact inv_mem hS.t_mem
  have hpoly := isQuasiGeodesicPolygon_fourGon_of_oneOneSides D []
    [RelLetter.comp () t, RelLetter.base f] (altWord t rest) s hlet
    (isOneOneSide_of_length_le_one (by simp)) (isOneOneSide_pair _ _ htf)
    (isOneOneSide_of_isGeodesicWord hgeo)
    (isOneOneSide_of_isGeodesicWord (isGeodesicWord_one_of_isGeodesicWord hs)) hclose
  have hread0 : (([] : List (RelLetter G Unit)) ++ [RelLetter.comp () t, RelLetter.base f] ++
      altWord t rest ++ revWord s)[0]? = some (RelLetter.comp () t) := by
    rfl
  have hread1 : (([] : List (RelLetter G Unit)) ++ [RelLetter.comp () t, RelLetter.base f] ++
      altWord t rest ++ revWord s)[1]? = some (RelLetter.base f) := by
    rfl
  have hcomp0 : IsComp () (([] : List (RelLetter G Unit)) ++
      [RelLetter.comp () t, RelLetter.base f] ++ altWord t rest ++ revWord s) 0 1 :=
    isComp_unit_of_reads hread0 (Or.inl rfl) (Or.inr ⟨f, hread1⟩)
  have hv1 : vertex (1 : G) (([] : List (RelLetter G Unit)) ++
      [RelLetter.comp () t, RelLetter.base f] ++ altWord t rest ++ revWord s) 1 = t := by
    have h := vertex_succ_of_getElem? (v := (1 : G)) hread0
    rw [vertex_zero, one_mul] at h
    exact h
  have htdeep4 : t ∉ D.relBall () (C * 4) := fun hmem =>
    hS.t_deep (relBall_mono_radius D () (by omega) hmem)
  have hnotiso : ¬ IsIsolated D.fam () 1 (([] : List (RelLetter G Unit)) ++
      [RelLetter.comp () t, RelLetter.base f] ++ altWord t rest ++ revWord s) 0 := by
    intro hiso
    have hball := hS.proj 4 1 _ hpoly () 0 1 hcomp0 hiso
    rw [vertex_zero, hv1, inv_one, one_mul] at hball
    exact htdeep4 hball
  obtain ⟨j, hj0, hjstart, hjconn⟩ : ∃ j, j ≠ 0 ∧
      IsCompStart () (([] : List (RelLetter G Unit)) ++
        [RelLetter.comp () t, RelLetter.base f] ++ altWord t rest ++ revWord s) j ∧
      Connected D.fam () 1 (([] : List (RelLetter G Unit)) ++
        [RelLetter.comp () t, RelLetter.base f] ++ altWord t rest ++ revWord s) 0 j := by
    by_contra hcon
    exact hnotiso ⟨⟨1, hcomp0⟩, fun j hj hjs hjc => hcon ⟨j, hj, hjs, hjc⟩⟩
  obtain ⟨g, hgread⟩ := exists_read_of_isCompStart hjstart
  have hjlt := (List.getElem?_eq_some_iff.mp hgread).1
  rw [length_fourGon] at hjlt
  have hc : (vertex (1 : G) (([] : List (RelLetter G Unit)) ++
      [RelLetter.comp () t, RelLetter.base f] ++ altWord t rest ++ revWord s) 0)⁻¹ *
      vertex (1 : G) (([] : List (RelLetter G Unit)) ++
        [RelLetter.comp () t, RelLetter.base f] ++ altWord t rest ++ revWord s) j
        ∈ D.fam () := hjconn
  rw [vertex_zero, inv_one, one_mul] at hc
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · -- `j = 1` reads `b₁`, a base letter
    have hj1 : j = 1 := by omega
    rw [hj1, hread1] at hgread
    simp at hgread
  rcases Nat.lt_or_ge j (2 + (altWord t rest).length) with hjr | hjr
  · -- a component of `a₂b₂ ⋯ aₙbₙ` connected to `a₁` contradicts Lemma 4.3
    exfalso
    obtain ⟨m, rfl⟩ : ∃ m, j = ([] : List (RelLetter G Unit)).length +
        [RelLetter.comp () t, RelLetter.base f].length + m :=
      ⟨j - 2, by simp only [List.length_nil, List.length_cons]; omega⟩
    have hm : m < (altWord t rest).length := by
      simp only [List.length_nil, List.length_cons] at hjr; omega
    have hrread : (altWord t rest)[m]? = some (RelLetter.comp () g) := by
      rw [← getElem?_fourGon_r' [] [RelLetter.comp () t, RelLetter.base f] (altWord t rest) s hm]
      exact hgread
    have hfsread : (altWord t (f :: rest))[2 + m]? = some (RelLetter.comp () g) := by
      show ([RelLetter.comp () t, RelLetter.base f] ++ altWord t rest)[
        [RelLetter.comp () t, RelLetter.base f].length + m]? = _
      rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact hrread
    have hstartA : IsCompStart () (altWord t (f :: rest)) (2 + m) :=
      ⟨2 + m + 1, isComp_singleton_of_isWThree_read (isWThree_altWord D t hfsH) hfsread⟩
    have hvW := vertex_fourGon_third ([] : List (RelLetter G Unit))
      [RelLetter.comp () t, RelLetter.base f] (altWord t rest) s (1 : G) (le_of_lt hm)
    simp only [RelLetter.listVal_nil, listVal_cons, RelLetter.val, mul_one, one_mul] at hvW
    rw [hvW] at hc
    have hconnA : Connected D.fam () 1 (altWord t (f :: rest)) 0 (2 + m) := by
      show (vertex (1 : G) (altWord t (f :: rest)) 0)⁻¹ *
        vertex (1 : G) (altWord t (f :: rest)) (2 + m) ∈ D.fam ()
      rw [vertex_zero, inv_one, one_mul, vertex_altWord_cons, one_mul]
      exact hc
    have hiso0 : IsIsolated D.fam () 1 (altWord t (f :: rest)) 0 := by
      have h := (altWord_isComp_isIsolated hS.C_pos hS.sum_bound hS.t_mem hS.t_deep hfsX hfsH
        (1 : G) (i := 0) (by simp)).2
      rwa [Nat.mul_zero] at h
    exact hiso0.2 (2 + m) (by omega) hstartA hconnA
  · -- a component of `q` connected to `a₁` is its first edge
    obtain ⟨k, rfl⟩ : ∃ k, j = ([] : List (RelLetter G Unit)).length +
        [RelLetter.comp () t, RelLetter.base f].length + (altWord t rest).length + k :=
      ⟨j - (2 + (altWord t rest).length), by simp only [List.length_nil, List.length_cons]; omega⟩
    have hk : k < s.length := by
      simp only [List.length_nil, List.length_cons] at hjlt; omega
    have hsread := getElem?_fourGon_s' ([] : List (RelLetter G Unit))
      [RelLetter.comp () t, RelLetter.base f] (altWord t rest) s hk
    rw [hsread] at hgread
    obtain ⟨g', hg'⟩ := exists_comp_of_invLetter_eq_comp (Option.some.inj hgread)
    have hvs := vertex_fourGon_opposite_closed ([] : List (RelLetter G Unit))
      [RelLetter.comp () t, RelLetter.base f] (altWord t rest) s hclose (s.length - k)
    rw [show s.length - (s.length - k) = k by omega] at hvs
    rw [hvs] at hc
    have hle := index_le_one_of_mem_coset hs (lam := ()) (i := s.length - k) (by omega)
      (by rw [inv_one, one_mul]; exact hc)
    have hk1 : s.length - 1 - k = 0 := by omega
    have hs0read : s[0]? = some (RelLetter.comp () g') := by
      rw [← hk1]
      exact List.getElem?_eq_some_iff.mpr ⟨by omega, hg'⟩
    have hv1s : vertex (1 : G) s 1 = g' := by
      have h := vertex_succ_of_getElem? (v := (1 : G)) hs0read
      rw [vertex_zero, one_mul] at h
      exact h
    have hg'mem : g' ∈ D.fam () := hs.1 _ (mem_of_getElem?_eq_some hs0read)
    have hxy : t⁻¹ * vertex (1 : G) s 1 ∈ D.fam () := by
      rw [hv1s]
      exact mul_mem (inv_mem hS.t_mem) hg'mem
    have hs' : IsGeodesicWord D (vertex (1 : G) s 1)
        (t * f * RelLetter.listVal (altWord t rest)) (s.drop 1) := by
      have h := geodesic_drop hs (k := 1) (by omega)
      rwa [listVal_altWord_cons] at h
    have hs'0 : ∀ g : G, (s.drop 1)[0]? ≠ some (RelLetter.comp () g) := by
      intro g hg
      rw [List.getElem?_drop] at hg
      exact not_consecutive_comp_of_isGeodesicWord hs hs0read hg
    obtain ⟨hlenR, hmatchR⟩ := hR t (vertex (1 : G) s 1) (s.drop 1) hxy hs' hs'0
    simp only [List.length_drop] at hlenR
    refine ⟨?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · intro i hi
      rcases i with _ | i'
      · refine ⟨0, le_refl _, ?_, ⟨g', hs0read⟩, ?_⟩
        · simp only [List.length_cons]
          omega
        · rw [Nat.mul_zero, vertex_zero, vertex_zero, inv_one, one_mul]
          exact one_mem _
      · obtain ⟨j'', hj''1, hj''2, ⟨g'', hg''⟩, hconn''⟩ :=
          hmatchR i' (by simp only [List.length_cons] at hi; omega)
        simp only [List.length_drop] at hj''2
        refine ⟨1 + j'', by omega, ?_, ⟨g'', ?_⟩, ?_⟩
        · simp only [List.length_cons]
          omega
        · rwa [List.getElem?_drop] at hg''
        · rw [show 2 * (i' + 1) = 2 + 2 * i' by ring, vertex_altWord_cons, one_mul,
            vertex_drop']
          exact hconn''

end FirstStep

section InductiveStep

variable {G : Type u} [Group G] {D : RelGenSet G Unit} {F : Set G} {t : G} {C : ℕ}

/-- **The inductive step of Lemma 4.4**: the pentagon `bᵢ, aᵢ₊₁, bᵢ₊₁ ⋯ aₙbₙ, (q')⁻¹, fᵢ`,
realised as the quadrilateral `[fᵢ, bᵢ] ++ aᵢ₊₁ ⋯ aₙbₙ ++ [] ++ revWord q'`.  `aᵢ₊₁` is
connected to a component `cᵢ₊₁` of `q'` which is not its first letter, and the state
after `cᵢ₊₁` continues the induction. -/
theorem goMatchState_cons (hS : GOSetting D F t C) {x y f f' : G} {rest' : List G}
    (hf : f ∈ F) (hf' : f' ∈ F) (hrest' : ∀ g ∈ rest', g ∈ F) (hxy : x⁻¹ * y ∈ D.fam ())
    (hgeo : IsGeodesicWord D 1 (RelLetter.listVal (altWord t (f' :: rest')))
      (altWord t (f' :: rest')))
    (hR : ∀ (x' y' : G) (s' : List (RelLetter G Unit)), x'⁻¹ * y' ∈ D.fam () →
      IsGeodesicWord D y' (x' * f' * RelLetter.listVal (altWord t rest')) s' →
      (∀ g : G, s'[0]? ≠ some (RelLetter.comp () g)) → GOMatchState D t x' y' f' rest' s')
    {s : List (RelLetter G Unit)}
    (hs : IsGeodesicWord D y (x * f * RelLetter.listVal (altWord t (f' :: rest'))) s)
    (hs0 : ∀ g : G, s[0]? ≠ some (RelLetter.comp () g)) :
    GOMatchState D t x y f (f' :: rest') s := by
  obtain ⟨h, hh, rfl⟩ : ∃ h : G, h ∈ D.fam () ∧ y * h = x := by
    refine ⟨y⁻¹ * x, ?_, by group⟩
    have e := inv_mem hxy
    rwa [mul_inv_rev, inv_inv] at e
  have hfX : f ∈ D.base := hS.F_base f hf
  have hfH : f ∉ D.fam () := hS.F_not_fam f hf
  have hfsX : ∀ g ∈ f' :: rest', g ∈ D.base := by
    intro g hg
    rcases List.mem_cons.mp hg with e | hg
    · rw [e]; exact hS.F_base _ hf'
    · exact hS.F_base g (hrest' g hg)
  have hfsH : ∀ g ∈ f' :: rest', g ∉ D.fam () := by
    intro g hg
    rcases List.mem_cons.mp hg with e | hg
    · rw [e]; exact hS.F_not_fam _ hf'
    · exact hS.F_not_fam g (hrest' g hg)
  have hval : RelLetter.listVal s = h * f * RelLetter.listVal (altWord t (f' :: rest')) := by
    have h2 : y * RelLetter.listVal s
        = y * (h * f * RelLetter.listVal (altWord t (f' :: rest'))) := by
      rw [hs.2.1]
      group
    exact mul_left_cancel h2
  have hclose : RelLetter.listVal s = RelLetter.listVal [RelLetter.comp () h, RelLetter.base f] *
      RelLetter.listVal (altWord t (f' :: rest')) *
      RelLetter.listVal ([] : List (RelLetter G Unit)) := by
    rw [hval]
    simp only [listVal_cons, RelLetter.listVal_nil, RelLetter.val, mul_one]
  have hlet : ∀ a ∈ [RelLetter.comp () h, RelLetter.base f] ++ altWord t (f' :: rest') ++
      ([] : List (RelLetter G Unit)) ++ revWord s, D.IsLetter a := by
    refine fourGon_letters hS.base_symm ?_ hgeo.1 (by simp) hs.1
    intro a ha
    rcases List.mem_cons.mp ha with e | ha
    · rw [e]; exact hh
    rcases List.mem_cons.mp ha with e | ha
    · rw [e]; exact hfX
    simp at ha
  have hhf : (RelLetter.comp () h : RelLetter G Unit).val * (RelLetter.base f : RelLetter G Unit).val ≠ 1 := by
    intro e
    apply hfH
    have e' : f = h⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [e']
    exact inv_mem hh
  have hpoly := isQuasiGeodesicPolygon_fourGon_of_oneOneSides D
    [RelLetter.comp () h, RelLetter.base f] (altWord t (f' :: rest')) [] s hlet
    (isOneOneSide_pair _ _ hhf) (isOneOneSide_of_isGeodesicWord hgeo)
    (isOneOneSide_of_length_le_one (by simp))
    (isOneOneSide_of_isGeodesicWord (isGeodesicWord_one_of_isGeodesicWord hs)) hclose
  have hread1 : ([RelLetter.comp () h, RelLetter.base f] ++ altWord t (f' :: rest') ++
      ([] : List (RelLetter G Unit)) ++ revWord s)[1]? = some (RelLetter.base f) := by
    rfl
  have hread2 : ([RelLetter.comp () h, RelLetter.base f] ++ altWord t (f' :: rest') ++
      ([] : List (RelLetter G Unit)) ++ revWord s)[2]? = some (RelLetter.comp () t) := by
    rfl
  have hread3 : ([RelLetter.comp () h, RelLetter.base f] ++ altWord t (f' :: rest') ++
      ([] : List (RelLetter G Unit)) ++ revWord s)[3]? = some (RelLetter.base f') := by
    rfl
  have hcomp2 : IsComp () ([RelLetter.comp () h, RelLetter.base f] ++ altWord t (f' :: rest') ++
      ([] : List (RelLetter G Unit)) ++ revWord s) 2 3 :=
    isComp_unit_of_reads hread2 (Or.inr ⟨f, hread1⟩) (Or.inr ⟨f', hread3⟩)
  have hv2 : vertex (1 : G) ([RelLetter.comp () h, RelLetter.base f] ++
      altWord t (f' :: rest') ++ ([] : List (RelLetter G Unit)) ++ revWord s) 2 = h * f := by
    have e := vertex_fourGon_side [RelLetter.comp () h, RelLetter.base f]
      (altWord t (f' :: rest')) ([] : List (RelLetter G Unit)) s (1 : G)
      (Nat.zero_le (altWord t (f' :: rest')).length)
    simp only [vertex_zero, mul_one, one_mul, listVal_cons, RelLetter.listVal_nil,
      RelLetter.val] at e
    exact e
  have hv3 : vertex (1 : G) ([RelLetter.comp () h, RelLetter.base f] ++
      altWord t (f' :: rest') ++ ([] : List (RelLetter G Unit)) ++ revWord s) 3
        = h * f * t := by
    have e := vertex_succ_of_getElem? (v := (1 : G)) hread2
    rw [hv2] at e
    exact e
  have htdeep4 : t ∉ D.relBall () (C * 4) := fun hmem =>
    hS.t_deep (relBall_mono_radius D () (by omega) hmem)
  have hnotiso : ¬ IsIsolated D.fam () 1 ([RelLetter.comp () h, RelLetter.base f] ++
      altWord t (f' :: rest') ++ ([] : List (RelLetter G Unit)) ++ revWord s) 2 := by
    intro hiso
    have hball := hS.proj 4 1 _ hpoly () 2 3 hcomp2 hiso
    rw [hv2, hv3, show (h * f)⁻¹ * (h * f * t) = t by group] at hball
    exact htdeep4 hball
  obtain ⟨j, hj2, hjstart, hjconn⟩ : ∃ j, j ≠ 2 ∧
      IsCompStart () ([RelLetter.comp () h, RelLetter.base f] ++ altWord t (f' :: rest') ++
        ([] : List (RelLetter G Unit)) ++ revWord s) j ∧
      Connected D.fam () 1 ([RelLetter.comp () h, RelLetter.base f] ++
        altWord t (f' :: rest') ++ ([] : List (RelLetter G Unit)) ++ revWord s) 2 j := by
    by_contra hcon
    exact hnotiso ⟨⟨3, hcomp2⟩, fun j hj hjs hjc => hcon ⟨j, hj, hjs, hjc⟩⟩
  obtain ⟨g, hgread⟩ := exists_read_of_isCompStart hjstart
  have hjlt := (List.getElem?_eq_some_iff.mp hgread).1
  rw [length_fourGon] at hjlt
  have hc : (vertex (1 : G) ([RelLetter.comp () h, RelLetter.base f] ++
      altWord t (f' :: rest') ++ ([] : List (RelLetter G Unit)) ++ revWord s) 2)⁻¹ *
      vertex (1 : G) ([RelLetter.comp () h, RelLetter.base f] ++
        altWord t (f' :: rest') ++ ([] : List (RelLetter G Unit)) ++ revWord s) j
        ∈ D.fam () := hjconn
  rw [hv2] at hc
  rcases Nat.lt_or_ge j 2 with hjlt2 | hjge2
  · exfalso
    rcases Nat.lt_or_ge j 1 with hj1 | hj1
    · -- `fᵢ` is connected to `aᵢ₊₁` only if `Lab(bᵢ) ∈ H`
      have hj0 : j = 0 := by omega
      rw [hj0, vertex_zero, mul_one] at hc
      apply hfH
      have e : f = h⁻¹ * (h * f)⁻¹⁻¹ := by group
      rw [e]
      exact mul_mem (inv_mem hh) (inv_mem hc)
    · have hj1' : j = 1 := by omega
      rw [hj1', hread1] at hgread
      simp at hgread
  rcases Nat.lt_or_ge j (2 + (altWord t (f' :: rest')).length) with hjq | hjq
  · -- a component of `aᵢ₊₁ ⋯ aₙbₙ` connected to `aᵢ₊₁` contradicts Lemma 4.3
    exfalso
    obtain ⟨i', rfl⟩ : ∃ i', j = [RelLetter.comp () h, RelLetter.base f].length + i' :=
      ⟨j - 2, by simp only [List.length_cons, List.length_nil]; omega⟩
    have hi' : i' < (altWord t (f' :: rest')).length := by
      simp only [List.length_cons, List.length_nil] at hjq; omega
    have hi'0 : i' ≠ 0 := by
      intro e
      apply hj2
      rw [e]
      rfl
    have hqread : (altWord t (f' :: rest'))[i']? = some (RelLetter.comp () g) := by
      rw [← getElem?_fourGon_q' [RelLetter.comp () h, RelLetter.base f]
        (altWord t (f' :: rest')) ([] : List (RelLetter G Unit)) s hi']
      exact hgread
    have hqstart : IsCompStart () (altWord t (f' :: rest')) i' :=
      ⟨i' + 1, isComp_singleton_of_isWThree_read (isWThree_altWord D t hfsH) hqread⟩
    have hqconn : Connected D.fam () 1 (altWord t (f' :: rest')) 0 i' :=
      (connected_fourGon_side_iff D () [RelLetter.comp () h, RelLetter.base f]
        (altWord t (f' :: rest')) ([] : List (RelLetter G Unit)) s (Nat.zero_le _)
        hi'.le).mp hjconn
    have hiso0 : IsIsolated D.fam () 1 (altWord t (f' :: rest')) 0 := by
      have e := (altWord_isComp_isIsolated hS.C_pos hS.sum_bound hS.t_mem hS.t_deep hfsX
        hfsH (1 : G) (i := 0) (by simp)).2
      rwa [Nat.mul_zero] at e
    exact hiso0.2 i' hi'0 hqstart hqconn
  · -- a component `cᵢ₊₁` of `q'` connected to `aᵢ₊₁`
    obtain ⟨k, rfl⟩ : ∃ k, j = [RelLetter.comp () h, RelLetter.base f].length +
        (altWord t (f' :: rest')).length + ([] : List (RelLetter G Unit)).length + k :=
      ⟨j - (2 + (altWord t (f' :: rest')).length),
        by simp only [List.length_cons, List.length_nil]; omega⟩
    have hk : k < s.length := by
      simp only [List.length_cons, List.length_nil] at hjlt; omega
    have hsread := getElem?_fourGon_s' [RelLetter.comp () h, RelLetter.base f]
      (altWord t (f' :: rest')) ([] : List (RelLetter G Unit)) s hk
    rw [hsread] at hgread
    obtain ⟨g', hg'⟩ := exists_comp_of_invLetter_eq_comp (Option.some.inj hgread)
    have hi0read : s[s.length - 1 - k]? = some (RelLetter.comp () g') :=
      List.getElem?_eq_some_iff.mpr ⟨by omega, hg'⟩
    have hconn' := (connected_fourGon_iff D () [RelLetter.comp () h, RelLetter.base f]
      (altWord t (f' :: rest')) ([] : List (RelLetter G Unit)) s hclose (i := 0)
      (j := s.length - k) (Nat.zero_le _)).mp (by
        rw [show [RelLetter.comp () h, RelLetter.base f].length +
            (altWord t (f' :: rest')).length + ([] : List (RelLetter G Unit)).length +
              (s.length - (s.length - k))
            = [RelLetter.comp () h, RelLetter.base f].length +
              (altWord t (f' :: rest')).length + ([] : List (RelLetter G Unit)).length + k
            by omega]
        exact hjconn)
    simp only [listVal_cons, RelLetter.listVal_nil, RelLetter.val, mul_one,
      vertex_zero] at hconn'
    have hidx : s.length - k = s.length - 1 - k + 1 := by omega
    rw [hidx, vertex_succ_of_getElem? (v := (1 : G)) hi0read] at hconn'
    have hg'mem : g' ∈ D.fam () := hs.1 _ (mem_of_getElem?_eq_some hi0read)
    have hconn0 : (h * f)⁻¹ * vertex (1 : G) s (s.length - 1 - k) ∈ D.fam () := by
      have e : (h * f)⁻¹ * vertex (1 : G) s (s.length - 1 - k)
          = (h * f)⁻¹ * (vertex (1 : G) s (s.length - 1 - k) * g') * g'⁻¹ := by group
      rw [e]
      exact mul_mem hconn' (inv_mem hg'mem)
    have hi0pos : s.length - 1 - k ≠ 0 := by
      intro e
      rw [e] at hi0read
      exact hs0 g' hi0read
    have hdrop := geodesic_drop hs (k := s.length - 1 - k + 1) (by omega)
    rw [listVal_altWord_cons] at hdrop
    have hend : y * h * f * (t * f' * RelLetter.listVal (altWord t rest'))
        = y * h * f * t * f' * RelLetter.listVal (altWord t rest') := by group
    rw [hend] at hdrop
    have hxy' : (y * h * f * t)⁻¹ * vertex y s (s.length - 1 - k + 1) ∈ D.fam () := by
      rw [vertex_eq_mul_vertex_one s y, vertex_succ_of_getElem? (v := (1 : G)) hi0read]
      have e : (y * h * f * t)⁻¹ *
          (y * (vertex (1 : G) s (s.length - 1 - k) * (RelLetter.comp () g').val))
          = t⁻¹ * ((h * f)⁻¹ * vertex (1 : G) s (s.length - 1 - k)) * g' := by
        simp only [RelLetter.val]
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hS.t_mem) hconn0) hg'mem
    have hs''0 : ∀ g : G, (s.drop (s.length - 1 - k + 1))[0]? ≠ some (RelLetter.comp () g) := by
      intro g hg
      rw [List.getElem?_drop] at hg
      exact not_consecutive_comp_of_isGeodesicWord hs hi0read hg
    obtain ⟨hlenR, hmatchR⟩ := hR (y * h * f * t) (vertex y s (s.length - 1 - k + 1))
      (s.drop (s.length - 1 - k + 1)) hxy' hdrop hs''0
    simp only [List.length_drop] at hlenR
    refine ⟨?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · intro k' hk'
      rcases k' with _ | k''
      · refine ⟨s.length - 1 - k, by omega, ?_, ⟨g', hi0read⟩, ?_⟩
        · simp only [List.length_cons]
          omega
        · rw [Nat.mul_zero, vertex_zero, mul_one, vertex_eq_mul_vertex_one s y]
          have e : (y * h * f)⁻¹ * (y * vertex (1 : G) s (s.length - 1 - k))
              = (h * f)⁻¹ * vertex (1 : G) s (s.length - 1 - k) := by group
          rw [e]
          exact hconn0
      · obtain ⟨j'', hj''1, hj''2, ⟨g'', hg''⟩, hconn''⟩ :=
          hmatchR k'' (by simp only [List.length_cons] at hk'; omega)
        simp only [List.length_drop] at hj''2
        refine ⟨s.length - 1 - k + 1 + j'', by omega, ?_, ⟨g'', ?_⟩, ?_⟩
        · simp only [List.length_cons]
          omega
        · rwa [List.getElem?_drop] at hg''
        · rw [show 2 * (k'' + 1) = 2 + 2 * k'' by ring, vertex_altWord_cons, one_mul,
            vertex_drop']
          have e : y * h * f * (t * f' * vertex (1 : G) (altWord t rest') (2 * k''))
              = y * h * f * t * f' * vertex (1 : G) (altWord t rest') (2 * k'') := by group
          rw [e]
          exact hconn''

end InductiveStep

section Assembly

variable {G : Type u} [Group G] {D : RelGenSet G Unit} {F : Set G} {t : G} {C : ℕ}

/-- The induction on `n` of Lemma 4.4, carrying the first step and the inductive state
together: the first step at `n + 1` uses the state at `n` and geodesicity of
`t f₂ ⋯ t fₙ₊₁`, and the state at `n + 1` uses geodesicity of `aᵢ₊₁ ⋯ aₙbₙ`, which is the
first step at `n + 1`. -/
theorem goLemma44_induction (hS : GOSetting D F t C) (n : ℕ) :
    (∀ fs : List G, fs.length = n → (∀ f ∈ fs, f ∈ F) →
      ∀ s : List (RelLetter G Unit),
        IsGeodesicWord D 1 (RelLetter.listVal (altWord t fs)) s → GOMatch D t fs s) ∧
    (∀ (x y f : G) (rest : List G) (s : List (RelLetter G Unit)), rest.length = n → f ∈ F →
      (∀ g ∈ rest, g ∈ F) → x⁻¹ * y ∈ D.fam () →
      IsGeodesicWord D y (x * f * RelLetter.listVal (altWord t rest)) s →
      (∀ g : G, s[0]? ≠ some (RelLetter.comp () g)) → GOMatchState D t x y f rest s) := by
  induction n with
  | zero =>
    refine ⟨fun fs hfs _ s _ => ?_, fun x y f rest s hrest hf _ hxy hs _ => ?_⟩
    · obtain rfl := List.length_eq_zero_iff.mp hfs
      exact goMatch_nil s
    · obtain rfl := List.length_eq_zero_iff.mp hrest
      exact goMatchState_nil hS hf hxy hs
  | succ n ih =>
    have hG : ∀ fs : List G, fs.length = n + 1 → (∀ f ∈ fs, f ∈ F) →
        ∀ s : List (RelLetter G Unit),
          IsGeodesicWord D 1 (RelLetter.listVal (altWord t fs)) s → GOMatch D t fs s := by
      intro fs hfs hfsF s hs
      obtain ⟨f, rest, rfl⟩ := List.exists_cons_of_length_eq_add_one hfs
      have hrest : rest.length = n := by simpa using hfs
      have hfF : f ∈ F := hfsF f List.mem_cons_self
      have hrestF : ∀ g ∈ rest, g ∈ F := fun g hg => hfsF g (List.mem_cons_of_mem f hg)
      exact goMatch_cons hS hfF hrestF
        (isGeodesicWord_altWord_of_match hS hrestF fun s' hs' =>
          (ih.1 rest hrest hrestF s' hs').1)
        (fun x y s' hxy hs' hs'0 => ih.2 x y f rest s' hrest hfF hrestF hxy hs' hs'0) hs
    refine ⟨hG, ?_⟩
    intro x y f rest s hrest hf hrestF hxy hs hs0
    obtain ⟨f', rest', rfl⟩ := List.exists_cons_of_length_eq_add_one hrest
    have hrest' : rest'.length = n := by simpa using hrest
    have hf' : f' ∈ F := hrestF f' List.mem_cons_self
    have hrest'F : ∀ g ∈ rest', g ∈ F := fun g hg => hrestF g (List.mem_cons_of_mem f' hg)
    exact goMatchState_cons hS hf hf' hrest'F hxy
      (isGeodesicWord_altWord_of_match hS hrestF fun s' hs' =>
        (hG (f' :: rest') hrest hrestF s' hs').1)
      (fun x' y' s' hx' hs' hs'0 => ih.2 x' y' f' rest' s' hrest' hf' hrest'F hx' hs' hs'0)
      hs hs0

/-- **Gerasimova–Osin, Lemma 4.4.**  A geodesic `q` from `p₋ = 1` to `p₊`, where
`Lab(p) = t f₁ ⋯ t fₙ`, decomposes as `c₁d₁ ⋯ cₙdₙ` with `cᵢ` connected to `aᵢ` and
every `dᵢ` nontrivial. -/
theorem gerasimovaOsinLemma44 (hS : GOSetting D F t C) {fs : List G} (hfs : ∀ f ∈ fs, f ∈ F)
    {s : List (RelLetter G Unit)}
    (hs : IsGeodesicWord D 1 (RelLetter.listVal (altWord t fs)) s) : GOMatch D t fs s :=
  (goLemma44_induction hS fs.length).1 fs rfl hfs s hs

/-- **Lemma 4.4, "in particular, the path `p` is geodesic".** -/
theorem isGeodesicWord_altWord (hS : GOSetting D F t C) {fs : List G}
    (hfs : ∀ f ∈ fs, f ∈ F) :
    IsGeodesicWord D 1 (RelLetter.listVal (altWord t fs)) (altWord t fs) :=
  isGeodesicWord_altWord_of_match hS hfs fun _ hs => (gerasimovaOsinLemma44 hS hfs hs).1

end Assembly

end GerasimovaOsinWords
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.GerasimovaOsinWords

#audit_axioms isQuasiGeodesicPolygon_fourGon_of_oneOneSides
#audit_axioms gerasimovaOsinLemma44
#audit_axioms isGeodesicWord_altWord
