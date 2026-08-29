import GroupApproximation.GGT.OsinTheorem54SepTwoBlockConj
import GroupApproximation.GGT.OsinTheorem54SepFourGonPolygon
import GroupApproximation.GGT.OsinTheorem54SepRotateComponent

/-!
# The second reading of the quadrilateral, derived

`exists_two_block_conj_of_innermost` bounds both gaps between two matched
blocks, and assumes the second linearisation of the polygon: a quasi-geodesic
polygon `(v₂,u₂)` carrying the two components in the other order.  That
assumption is discharged here.

Everything it asked for is now produced from the first reading:

* the polygon --- `isQuasiGeodesicPolygon_fourGon_rot`, the quadrilateral turned
  round at the corner `|p| + |q|`, which always lies in the arc between the two
  components, so the rotation costs no sides;
* the two components --- `isComp_rotWord_after` for the one on the reversed side
  `s`, which lies past the corner, and `isComp_rotWord_before` for the one on
  `q`, which lies before it;
* the connectedness and the two vertex identifications --- `vertex_rotWord_le`
  and `vertex_rotWord_add`, the second of which is where the closing relation is
  spent.

## What is still assumed, and why it is not a debt

The innermost clause of the second reading.  It says that no component start
lying in the OTHER arc --- the one running from the end of the `s`-component,
through the basepoint, to the start of the `q`-component --- is connected to the
`s`-component.  That is information about the configuration, not about the
geometry: it is the same kind of hypothesis as the innermost clause of the first
reading, which `DGOIsolatedComponentCut.connector_mem_relBall` requires and
which no theorem supplies either.  It is stated in the rotated word's own
coordinates because that is where the cut bound reads it.

`0 < p.length` is the other addition, and it is one hypothesis doing two jobs:
it puts a base letter at the polygon's basepoint, which is what stops the
`s`-component from running past the end of the word into the `q`-block when
`j = 0`, and what stops the `q`-component from starting at the basepoint.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Both gaps of a matched pair of blocks are short, from one reading of the
polygon.**

`exists_two_block_conj_of_innermost` with its second polygon supplied rather
than assumed.  The quasi-geodesic hypothesis is the clause at the
quadrilateral's own corners, which is what a caller verifies anyway and is
strictly more than the packaged predicate says. -/
theorem exists_two_block_conj_of_rot (D : RelGenSet G Λ) (lam : Λ)
    (hbound : ∀ mu b : ℝ, 1 ≤ mu → 0 ≤ b → ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (mu b : ℝ) (hmu : 1 ≤ mu)
    (hb : 0 ≤ b) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (p q r s : List (RelLetter G Λ)) (i k j l : ℕ),
        RelLetter.listVal s = RelLetter.listVal p * RelLetter.listVal q
            * RelLetter.listVal r →
        (∀ a ∈ p ++ q ++ r ++ revWord s, D.IsLetter a) →
        (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
        (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
        0 < p.length →
        (∀ t : ℕ, t < 4 → ∀ x y : ℕ, fourGonCut p q r s t ≤ x → x ≤ y →
          y ≤ fourGonCut p q r s (t + 1) →
          ((y - x : ℕ) : ℝ) / mu - b
            ≤ ((wordDist D.alphabet.carrier
                (vertex (1 : G) (p ++ q ++ r ++ revWord s) x)
                (vertex (1 : G) (p ++ q ++ r ++ revWord s) y) : ℕ) : ℝ)) →
        IsComp lam q i k → (k < q.length ∨ 0 < r.length) →
        IsComp lam s j l → (l < s.length ∨ 0 < r.length) →
        Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i)
            (p.length + q.length + r.length + (s.length - l)) →
        (∀ t : ℕ, p.length + i < t →
          t < p.length + q.length + r.length + (s.length - l) →
          IsCompStart lam (p ++ q ++ r ++ revWord s) t →
          ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
            (p.length + i) t) →
        (∀ t : ℕ,
          p.length + q.length + r.length + (s.length - l)
              - (p.length + q.length) < t →
          t < (p ++ q ++ r ++ revWord s).length - (p.length + q.length)
              + (p.length + i) →
          IsCompStart lam
            (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length)) t →
          ¬ Connected D.fam lam
              (vertex (1 : G) (p ++ q ++ r ++ revWord s)
                (p.length + q.length))
              (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length))
              (p.length + q.length + r.length + (s.length - l)
                - (p.length + q.length)) t) →
        ∃ x x' : G, x ∈ D.relBall lam (C * 4) ∧ x' ∈ D.relBall lam (C * 4) ∧
          x * ((vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k) * x'
            = (vertex (1 : G) s j)⁻¹ * vertex (1 : G) s l := by
  obtain ⟨C, hCpos, hC⟩ :=
    exists_two_block_conj_of_innermost D lam hbound hsymm mu b hmu hb
  refine ⟨C, hCpos, ?_⟩
  intro p q r s i k j l hclose hlet hp hr hp0 hqg hcompq hkq hcomps hlq hconn
    hinner hinner₂
  -- the polygon, and the same polygon read from the corner between `q` and `r`
  have hpoly := isQuasiGeodesicPolygon_fourGon p q r s D hlet hclose hqg
  have hpoly₂ := isQuasiGeodesicPolygon_fourGon_rot p q r s D hlet hclose hqg
  have hclosedW : RelLetter.listVal (p ++ q ++ r ++ revWord s) = 1 :=
    listVal_fourGon_eq_one p q r s hclose
  have hlenW : (p ++ q ++ r ++ revWord s).length
      = p.length + q.length + r.length + s.length := length_fourGon p q r s
  have hiq : i < q.length := lt_of_lt_of_le hcompq.1 hcompq.2.1
  have hkle : k ≤ q.length := hcompq.2.1
  have hjl : j < l := hcomps.1
  have hls : l ≤ s.length := hcomps.2.1
  have hcW : p.length + q.length ≤ (p ++ q ++ r ++ revWord s).length := by omega
  -- the two components, carried into the rotated word
  have hbridgeq := isComp_fourGon_of_isComp_side p q r s lam hp hr hcompq hkq
  have hbridges := isComp_fourGon_of_isComp_opposite p q r s lam hr hcomps hlq
  have hwrap : ∀ h0 : 0 < (p ++ q ++ r ++ revWord s).length,
      p.length + q.length + r.length + (s.length - j)
        = (p ++ q ++ r ++ revWord s).length →
      ¬ ((p ++ q ++ r ++ revWord s)[0]'h0).IsCompOf lam :=
    fun h0 _ => notIsCompOf_fourGon_zero p q r s lam hp hp0 h0
  have hrotS := isComp_rotWord_after lam hcW hbridges (by omega) hwrap
  have hrotQ := isComp_rotWord_before lam hcW hbridgeq (by omega) (by omega)
  -- the three vertex identifications
  have hvS : vertex (vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + q.length))
      (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length))
      (p.length + q.length + r.length + (s.length - l)
        - (p.length + q.length))
      = vertex (1 : G) s l := by
    rw [vertex_rotWord_le 1 (p ++ q ++ r ++ revWord s) hcW
        (p.length + q.length + r.length + (s.length - l)
          - (p.length + q.length)) (by omega),
      show p.length + q.length + (p.length + q.length + r.length
          + (s.length - l) - (p.length + q.length))
        = p.length + q.length + r.length + (s.length - l) from by omega,
      vertex_fourGon_opposite_closed p q r s hclose l]
  have hvE : vertex (vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + q.length))
      (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length))
      (p.length + q.length + r.length + (s.length - j)
        - (p.length + q.length))
      = vertex (1 : G) s j := by
    rw [vertex_rotWord_le 1 (p ++ q ++ r ++ revWord s) hcW
        (p.length + q.length + r.length + (s.length - j)
          - (p.length + q.length)) (by omega),
      show p.length + q.length + (p.length + q.length + r.length
          + (s.length - j) - (p.length + q.length))
        = p.length + q.length + r.length + (s.length - j) from by omega,
      vertex_fourGon_opposite_closed p q r s hclose j]
  have hvQ : vertex (vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + q.length))
      (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length))
      ((p ++ q ++ r ++ revWord s).length - (p.length + q.length)
        + (p.length + i))
      = RelLetter.listVal p * vertex (1 : G) q i := by
    rw [vertex_rotWord_add 1 (p ++ q ++ r ++ revWord s) hcW hclosedW
        ((p ++ q ++ r ++ revWord s).length - (p.length + q.length)
          + (p.length + i)) (p.length + i) rfl (by omega),
      vertex_fourGon_side p q r s 1 (le_of_lt hiq), one_mul]
  -- connectedness in the rotated word
  have hconn₂ : Connected D.fam lam
      (vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + q.length))
      (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length))
      (p.length + q.length + r.length + (s.length - l)
        - (p.length + q.length))
      ((p ++ q ++ r ++ revWord s).length - (p.length + q.length)
        + (p.length + i)) := by
    have hsym := connected_symm hconn
    have hvS' : vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + q.length + r.length + (s.length - l))
        = vertex (1 : G) s l :=
      vertex_fourGon_opposite_closed p q r s hclose l
    have hvQ' : vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + i)
        = RelLetter.listVal p * vertex (1 : G) q i := by
      rw [vertex_fourGon_side p q r s 1 (le_of_lt hiq), one_mul]
    show (vertex _ _ _)⁻¹ * vertex _ _ _ ∈ D.fam lam
    rw [hvS, hvQ]
    have hsym' : (vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + q.length + r.length + (s.length - l)))⁻¹ *
        vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + i)
      ∈ D.fam lam := hsym
    rwa [hvS', hvQ'] at hsym'
  exact hC p q r s i k j l hclose hp hr hpoly hcompq hkq hcomps hlq hconn hinner
    (vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + q.length))
    (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length))
    (p.length + q.length + r.length + (s.length - l) - (p.length + q.length))
    (p.length + q.length + r.length + (s.length - j) - (p.length + q.length))
    ((p ++ q ++ r ++ revWord s).length - (p.length + q.length)
      + (p.length + i))
    ((p ++ q ++ r ++ revWord s).length - (p.length + q.length)
      + (p.length + k))
    hpoly₂ hrotS hrotQ (by omega) hconn₂ hinner₂ hvE hvQ

end OsinComponents
end GGT
end GroupApproximation
