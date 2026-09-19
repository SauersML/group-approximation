import GroupApproximation.GGT.OsinTheorem54SepFourGonPolygon
import GroupApproximation.GGT.OsinTheorem54SepCommIndex

/-!
# A quadrilateral of geodesic sides is a geodesic polygon

Osin's Lemmas 4.8 and 4.9 are about polygons whose sides are GEODESICS: 4.8
compares two geodesics with the same endpoints, 4.9 compares the three sides of
a geodesic triangle.  Both are instances of the quadrilateral this development
already has --- the bigon is `p ++ q ++ r ++ revWord s` with `p` and `r` empty,
the triangle is the same with `p` empty --- so what they need is not a new cut
function but the clause: four geodesic sides make a `(1,0)`-quasi-geodesic
`4`-gon.

That is proved here, once, from `OsinTheorem54SepPolygon.sub_le_wordDist_vertex`
--- a geodesic word's sub-segments are geodesic --- plus the four block-vertex
identifications and left-invariance of the word metric.  The empty sides of the
degenerate cases cost nothing: an empty block contributes an interval of length
zero, on which the clause is vacuous.

## The fourth side is read backwards

Three of the four blocks translate directly.  The fourth is `revWord s`, whose
index `|p|+|q|+|r| + (|s| - j)` runs DOWN the side as the polygon index runs up,
so the inequality is applied to `s` at the reversed pair and turned round by
symmetry of the word metric.  That is the only asymmetry, and it is the same one
`vertex_fourGon_opposite_closed` already carries.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A geodesic side, translated, satisfies the `(1,0)` clause.**  The
translation is where the block's position in the polygon goes. -/
theorem geodesic_side_clause (D : RelGenSet G Λ) (u : List (RelLetter G Λ))
    (f : G) {a c : ℕ} (hgu : IsGeodesicWord D 1 (RelLetter.listVal u) u)
    (hac : a ≤ c) (hc : c ≤ u.length) :
    ((c - a : ℕ) : ℝ) / 1 - 0
      ≤ ((wordDist D.alphabet.carrier (f * vertex (1 : G) u a)
          (f * vertex (1 : G) u c) : ℕ) : ℝ) := by
  have hnat := sub_le_wordDist_vertex D hgu a c hac hc
  rw [wordDist_left_invariant]
  have hcast : ((c - a : ℕ) : ℝ)
      ≤ ((wordDist D.alphabet.carrier (vertex (1 : G) u a)
          (vertex (1 : G) u c) : ℕ) : ℝ) := Nat.cast_le.mpr hnat
  simp only [div_one, sub_zero]
  exact hcast

/-- **A quadrilateral of geodesic sides is a `(1,0)`-quasi-geodesic `4`-gon.**

The bigon and the triangle of Osin's §4 are the cases `p = r = []` and
`p = []`. -/
theorem isQuasiGeodesicPolygon_fourGon_of_geodesic (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (p q r s : List (RelLetter G Λ))
    (hgp : IsGeodesicWord D 1 (RelLetter.listVal p) p)
    (hgq : IsGeodesicWord D 1 (RelLetter.listVal q) q)
    (hgr : IsGeodesicWord D 1 (RelLetter.listVal r) r)
    (hgs : IsGeodesicWord D 1 (RelLetter.listVal s) s)
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r) :
    IsQuasiGeodesicPolygon D 1 0 4 1 (p ++ q ++ r ++ revWord s) := by
  refine isQuasiGeodesicPolygon_fourGon p q r s D ?_ hclose ?_
  · intro a ha
    rcases List.mem_append.mp ha with ha1 | ha1
    · rcases List.mem_append.mp ha1 with ha2 | ha2
      · rcases List.mem_append.mp ha2 with ha3 | ha3
        · exact hgp.1 a ha3
        · exact hgq.1 a ha3
      · exact hgr.1 a ha2
    · exact isLetter_of_mem_revWord D hsymm hgs.1 a ha1
  · intro t ht x y hx hxy hy
    by_cases h0 : t = 0
    · -- the first block is `p`
      subst h0
      have hy' : y ≤ p.length := hy
      rw [vertex_fourGon_first p q r s 1 (by omega),
        vertex_fourGon_first p q r s 1 hy']
      have h := geodesic_side_clause D p 1 hgp hxy hy'
      rw [one_mul, one_mul] at h
      exact h
    · by_cases h1 : t = 1
      · -- the second block is `q`
        subst h1
        have hx' : p.length ≤ x := hx
        have hy' : y ≤ p.length + q.length := hy
        obtain ⟨x', rfl⟩ : ∃ x', x = p.length + x' := ⟨x - p.length, by omega⟩
        obtain ⟨y', rfl⟩ : ∃ y', y = p.length + y' := ⟨y - p.length, by omega⟩
        rw [vertex_fourGon_side p q r s 1 (by omega : x' ≤ q.length),
          vertex_fourGon_side p q r s 1 (by omega : y' ≤ q.length), one_mul,
          show p.length + y' - (p.length + x') = y' - x' from by omega]
        exact geodesic_side_clause D q (RelLetter.listVal p) hgq (by omega)
          (by omega)
      · by_cases h2 : t = 2
        · -- the third block is `r`
          subst h2
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
          exact geodesic_side_clause D r
            (RelLetter.listVal p * RelLetter.listVal q) hgr (by omega) (by omega)
        · -- the fourth block is `s`, read backwards
          have ht3 : t = 3 := by omega
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
          have h := geodesic_side_clause D s 1 hgs
            (by omega : s.length - c ≤ s.length - a) (by omega)
          rw [one_mul, one_mul] at h
          exact h

end OsinComponents
end GGT
end GroupApproximation
