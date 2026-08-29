import GroupApproximation.GGT.DGOPolygonJoin
import GroupApproximation.GGT.OsinTheorem54SepPolygon

/-!
# The 4-gon cut off by a chord, and Case A of Lemma 4.17

Dahmani--Guirardel--Osin cut an `n`-gon at the corners `x₀` and `x₃` by a
geodesic `q`, and the near side of the cut is the 4-gon `p₀ p₁ p₂ q`.  This
module builds that 4-gon as polygon data — cut function, endpoints, monotonicity,
the quasi-geodesic clause — and closes **Case A**: when no component of the chord
is connected to the distinguished one, the 4-gon carries it as an isolated first
side and the base case applies directly.

Concept grep before writing: `isGeodesicWord_revWord` already exists
(`OsinTheorem54SepCommIndex`) and is not rewritten here; the chord is taken as a
geodesic word from `x₃` to `v`, which is what `existsGeodesicWord`
(`OsinGeodesicWord`) produces with the endpoints in that order, so no reversal is
needed at all.

## The clause on the chord's side

Sides `1` and `2` of the 4-gon are sides of the original polygon, read at the
same vertices, so their clause is quoted.  Side `3` is the chord, and its clause
is `sub_le_wordDist_vertex` (`OsinTheorem54SepPolygon`): a sub-path of a geodesic
word is geodesic, which at `(μ,b) = (1,0)` is exactly the clause.  Nothing about
hyperbolicity enters; the cut is metric-free.

## Why `c 1 < c 3`

The distinguished component ends at `c 1`, and for it to remain maximal in the
4-gon the letter at `c 1` must be a letter of `w` rather than the chord's first.
That is `c 1 < c 3`, which `DGOPolygonJoin.baseCase_of_dropEmpty` supplies by
shedding trivial sides before the cut is made.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The component survives the cut -/

omit [Group G] in
/-- **A component ending strictly inside the prefix is a component of the joined
word.**  Its letters and both its boundary letters are letters of `w`. -/
theorem isComp_joinWord (lam : Λ) {w : List (RelLetter G Λ)} {m : ℕ}
    {q : List (RelLetter G Λ)} (hm : m ≤ w.length) {i k : ℕ}
    (hcomp : IsComp lam w i k) (hkm : k < m) :
    IsComp lam (joinWord w m q) i k := by
  have hik : i < k := hcomp.1
  have hrange := hcomp.2.2.1
  have hprev := hcomp.2.2.2.1
  have hnext := hcomp.2.2.2.2
  have hlen : (joinWord w m q).length = m + q.length := length_joinWord w q hm
  refine ⟨hik, by omega, ?_, ?_, ?_⟩
  · intro p hp1 hp2 hpw
    rw [getElem_joinWord_lt w q hm p (by omega) hpw (by omega)]
    exact hrange p hp1 hp2 (by omega)
  · intro p hp hpw hc
    rw [getElem_joinWord_lt w q hm p (by omega) hpw (by omega)] at hc
    exact hprev p hp (by omega) hc
  · intro hk hc
    rw [getElem_joinWord_lt w q hm k hkm hk (by omega)] at hc
    exact hnext (by omega) hc

/-! ## The 4-gon -/

/-- **The cut polygon is a `(1,0)`-quasi-geodesic 4-gon.**

Its corners are `0, c 1, c 2, c 3` and the far end of the chord.  Sides `1` and
`2` quote the original clause; side `3` is the chord and quotes
`sub_le_wordDist_vertex`. -/
theorem exists_fourGon_cut (D : RelGenSet G Λ) (v : G)
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} {n : ℕ} {q : List (RelLetter G Λ)}
    (hc0 : c 0 = 0) (hcn : c n = w.length) (hcmono : ∀ s : ℕ, c s ≤ c (s + 1))
    (h3n : 3 ≤ n)
    (hclause : ∀ s : ℕ, s < n → s ≠ 0 → ∀ p q' : ℕ, c s ≤ p → p ≤ q' →
      q' ≤ c (s + 1) → ((q' - p : ℕ) : ℝ) / 1 - 0
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q') : ℕ) : ℝ))
    (hq : IsGeodesicWord D (vertex v w (c 3)) v q) :
    ∃ d : ℕ → ℕ, d 0 = 0 ∧ d 1 = c 1 ∧
      d 4 = (joinWord w (c 3) q).length ∧ (∀ s : ℕ, d s ≤ d (s + 1)) ∧
      ∀ s : ℕ, s < 4 → s ≠ 0 → ∀ p q' : ℕ, d s ≤ p → p ≤ q' →
        q' ≤ d (s + 1) → ((q' - p : ℕ) : ℝ) / 1 - 0
          ≤ ((wordDist D.alphabet.carrier
              (vertex v (joinWord w (c 3) q) p)
              (vertex v (joinWord w (c 3) q) q') : ℕ) : ℝ) := by
  have hmono : Monotone c := monotone_nat_of_le_succ hcmono
  have hc3w : c 3 ≤ w.length := by
    have h := hmono h3n
    rw [hcn] at h
    exact h
  have hlen : (joinWord w (c 3) q).length = c 3 + q.length :=
    length_joinWord w q hc3w
  set d : ℕ → ℕ := fun s => if s ≤ 3 then c s else c 3 + q.length
  have hdv : ∀ s : ℕ, d s = if s ≤ 3 then c s else c 3 + q.length := fun s => rfl
  have hdle : ∀ s : ℕ, s ≤ 3 → d s = c s := by
    intro s hs
    rw [hdv s, if_pos hs]
  have hdgt : ∀ s : ℕ, 3 < s → d s = c 3 + q.length := by
    intro s hs
    rw [hdv s, if_neg (by omega)]
  refine ⟨d, by rw [hdle 0 (by omega), hc0], hdle 1 (by omega),
    by rw [hdgt 4 (by omega), hlen], ?_, ?_⟩
  · intro s
    rcases Nat.lt_or_ge s 3 with hs | hs
    · rw [hdle s (by omega), hdle (s + 1) (by omega)]
      exact hcmono s
    · rcases Nat.eq_or_lt_of_le hs with hs3 | hs3
      · rw [hdle s (by omega), hdgt (s + 1) (by omega), ← hs3]
        omega
      · exact le_of_eq (by rw [hdgt s hs3, hdgt (s + 1) (by omega)])
  · intro s hs hs0 p q' hp hpq hq'
    rcases Nat.lt_or_ge s 3 with hs3 | hs3
    · -- a side of the original polygon, read at the same vertices
      rw [hdle s (by omega)] at hp
      rw [hdle (s + 1) (by omega)] at hq'
      have hqc : q' ≤ c 3 := le_trans hq' (hmono (by omega))
      rw [vertex_joinWord_le v w q hc3w p (by omega),
        vertex_joinWord_le v w q hc3w q' hqc]
      exact hclause s (by omega) hs0 p q' hp hpq hq'
    · -- the chord, whose clause is that a sub-path of a geodesic is geodesic
      have hs3' : s = 3 := by omega
      rw [hs3', hdle 3 le_rfl] at hp
      rw [hs3', hdgt 4 (by omega)] at hq'
      have hkey := sub_le_wordDist_vertex D hq (p - c 3) (q' - c 3) (by omega)
        (by omega)
      rw [vertex_joinWord_add v w q hc3w p (p - c 3) (by omega),
        vertex_joinWord_add v w q hc3w q' (q' - c 3) (by omega)]
      rw [div_one, sub_zero]
      have hcast : (q' - p : ℕ)
          ≤ wordDist D.alphabet.carrier
            (vertex (vertex v w (c 3)) q (p - c 3))
            (vertex (vertex v w (c 3)) q (q' - c 3)) := by
        have he : q' - c 3 - (p - c 3) = q' - p := by omega
        rwa [he] at hkey
      exact_mod_cast hcast

/-! ## Case A of Lemma 4.17 -/

/-- **Case A**: the distinguished component is isolated in the cut 4-gon.

DGO cut the `n`-gon by a geodesic `q` from `x₃` to `x₀`, and the near side of the
cut is the 4-gon `p₀ p₁ p₂ q`.  Its first side still carries the distinguished
component, by `isComp_joinWord`, and that component is still isolated, by
`isIsolated_joinWord`, exactly when no component of the chord is connected to it
--- which is the hypothesis `hchord` defining Case A.  The 4-gon base case then
bounds the span, with no dependence on `n`.

`c 1 < c 3` is what keeps the component maximal after the cut: the letter at
`c 1` must still be a letter of `w`.  `DGOPolygonJoin.baseCase_of_dropEmpty`
supplies it by shedding trivial sides first. -/
theorem span_mem_relBall_of_noChordConnection (D : RelGenSet G Λ) (C : ℕ)
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
    (hchord : ∀ t : ℕ, IsCompStart lam q t →
      ¬ Connected D.fam lam v (joinWord w (c 3) q) (c 0) (c 3 + t)) :
    (vertex v w (c 0))⁻¹ * vertex v w (c 1) ∈ D.relBall lam (C * 4) := by
  have hmono : Monotone c := monotone_nat_of_le_succ hcmono
  have hc3w : c 3 ≤ w.length := by
    have h := hmono h3n
    rw [hcn] at h
    exact h
  obtain ⟨d, hd0, hd1, hd4, hdmono, hdqg⟩ :=
    exists_fourGon_cut D v hc0 hcn hcmono h3n hcqg hq
  have hd0c : d 0 = c 0 := by rw [hd0, hc0]
  have hqval : RelLetter.listVal q = (vertex v w (c 3))⁻¹ * v :=
    eq_inv_mul_of_mul_eq hq.2.1
  have hcompJ : IsComp lam (joinWord w (c 3) q) (c 0) (c 1) :=
    isComp_joinWord lam hc3w hcomp hc13
  have hisoJ : IsIsolated D.fam lam v (joinWord w (c 3) q) (c 0) :=
    isIsolated_joinWord D lam v hc3w (by omega) ⟨_, hcompJ⟩ hiso hchord
  have hkey := hbase v (joinWord w (c 3) q) d
    (letters_joinWord D hlet (c 3) hq.1)
    (listVal_joinWord_eq_one v w (c 3) q hqval) hd0 hd4 hdmono lam hdqg
    (by rw [hd0c, hd1]; exact hcompJ) (by rw [hd0c]; exact hisoJ)
  have hv0 : vertex v (joinWord w (c 3) q) (d 0) = vertex v w (c 0) := by
    rw [hd0c, vertex_joinWord_le v w q hc3w (c 0) (by omega)]
  have hv1 : vertex v (joinWord w (c 3) q) (d 1) = vertex v w (c 1) := by
    rw [hd1, vertex_joinWord_le v w q hc3w (c 1) (by omega)]
  rw [← hv0, ← hv1]
  exact hkey

end OsinComponents
end GGT
end GroupApproximation
