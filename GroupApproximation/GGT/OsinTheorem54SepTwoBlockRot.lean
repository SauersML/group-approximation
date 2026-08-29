import GroupApproximation.GGT.DGOIsolatedComponentCut
import GroupApproximation.GGT.OsinTheorem54SepBlockConj
import GroupApproximation.GGT.OsinTheorem54SepFourGonOpposite
import GroupApproximation.GGT.OsinTheorem54SepFourGonPolygon
import GroupApproximation.GGT.OsinTheorem54SepRotateComponent

/-!
# The second reading of the quadrilateral, derived

Two components of a quadrilateral, one on each long side, matched to each
other, with BOTH connecting elements in a relative ball of radius `4C`, and
`x * v_q * x' = v_s` between them.

The two gaps are the two arcs of a CYCLIC object, and a word is a linearisation:
it cuts one of them.  Whichever arrangement of the four sides is written down,
one gap runs from the end of one component to the start of the other INSIDE the
word --- `DGOIsolatedComponentCut.connector_mem_relBall` bounds it --- while the
other runs through the basepoint, where no ordering of indices exhibits it as an
end-to-start pair.  So the polygon is read twice, and the second reading is
produced here rather than assumed:

* the polygon --- `isQuasiGeodesicPolygon_fourGon_rot`, the quadrilateral turned
  round at the corner `|p| + |q|`, which always lies in the arc between the two
  components (the `q`-component ends at or before it, the reversed-`s` component
  starts at or after `|p| + |q| + |r|`), so the rotation costs no sides;
* the two components --- `isComp_rotWord_after` for the one on the reversed side
  `s`, which lies past the corner, and `isComp_rotWord_before` for the one on
  `q`, which lies before it;
* the connectedness and the two vertex identifications --- `vertex_rotWord_le`
  and `vertex_rotWord_add`, the second of which is where the closing relation is
  spent;
* the innermost clause of the second reading, translated out of the rotated
  word's coordinates by `exists_isCompStart_of_rotWord_of_le`, so that the
  caller states it about `p ++ q ++ r ++ revWord s` and never meets `rotWord`
  at all.

## What is still assumed, and why it is not a debt

The innermost clause itself, in the caller's own coordinates: no component start
of the quadrilateral lying in the OTHER arc --- past the `s`-component, through
the end of the word and back to the start of the `q`-component --- is connected
to the `s`-component.  The two ranges of that hypothesis are exactly the two
halves of the rotated word, which is why the translation is an implication and
not an accident.

That is information about the configuration, not about the geometry: the same
kind of hypothesis as the innermost clause of the first reading, which
`DGOIsolatedComponentCut.connector_mem_relBall` requires and which no theorem
supplies either.

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

Both gaps come from one application each of the innermost end-to-start cut,
flipped by `connector_inv_mem_relBall`, and `block_span_conj` puts them either
side of the deep span --- which stays between them and is never folded in, being
unbounded while they are not.

The quasi-geodesic hypothesis is the clause at the quadrilateral's own corners,
which is what a caller verifies anyway and is strictly more than the packaged
predicate says. -/
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
        (∀ o : ℕ,
          (p.length + q.length + r.length + (s.length - l) < o
              ∧ o < (p ++ q ++ r ++ revWord s).length)
            ∨ o < p.length + i →
          IsCompStart lam (p ++ q ++ r ++ revWord s) o →
          ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
            (p.length + q.length + r.length + (s.length - l)) o) →
        ∃ x x' : G, x ∈ D.relBall lam (C * 4) ∧ x' ∈ D.relBall lam (C * 4) ∧
          x * ((vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k) * x'
            = (vertex (1 : G) s j)⁻¹ * vertex (1 : G) s l := by
  obtain ⟨C, hCpos, hC⟩ := connector_mem_relBall D hbound mu b hmu hb
  refine ⟨C, hCpos, ?_⟩
  intro p q r s i k j l hclose hlet hp hr hp0 hqg hcompq hkq hcomps hlq hconn
    hinner hother
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
  have hvSw : vertex (vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + q.length))
      (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length))
      (p.length + q.length + r.length + (s.length - l)
        - (p.length + q.length))
      = vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + q.length + r.length + (s.length - l)) := by
    rw [vertex_rotWord_le 1 (p ++ q ++ r ++ revWord s) hcW
        (p.length + q.length + r.length + (s.length - l)
          - (p.length + q.length)) (by omega),
      show p.length + q.length + (p.length + q.length + r.length
          + (s.length - l) - (p.length + q.length))
        = p.length + q.length + r.length + (s.length - l) from by omega]
  have hvS : vertex (vertex (1 : G) (p ++ q ++ r ++ revWord s)
        (p.length + q.length))
      (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length))
      (p.length + q.length + r.length + (s.length - l)
        - (p.length + q.length))
      = vertex (1 : G) s l := by
    rw [hvSw, vertex_fourGon_opposite_closed p q r s hclose l]
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
  -- the gap from the end of the `q`-block to the start of the `s`-block
  have happ1 := hC 4 (by omega) 1 (p ++ q ++ r ++ revWord s) hpoly lam
    (p.length + i) (p.length + k)
    (p.length + q.length + r.length + (s.length - l))
    (p.length + q.length + r.length + (s.length - j))
    hbridgeq hbridges (by omega) hconn hinner
  have hflip1 := connector_inv_mem_relBall D lam hsymm happ1
  rw [vertex_fourGon_side p q r s 1 hkle, one_mul,
    vertex_fourGon_opposite_closed p q r s hclose l] at hflip1
  -- the other arc's clause, carried into the rotated reading
  have hinner₂ : ∀ t : ℕ,
      p.length + q.length + r.length + (s.length - l)
          - (p.length + q.length) < t →
      t < (p ++ q ++ r ++ revWord s).length - (p.length + q.length)
          + (p.length + i) →
      IsCompStart lam
        (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length)) t →
      ¬ Connected D.fam lam
          (vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + q.length))
          (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length))
          (p.length + q.length + r.length + (s.length - l)
            - (p.length + q.length)) t := by
    intro t ht1 ht2 hstart hconnt
    obtain ⟨o, hostart, hbranch, hvo⟩ :=
      exists_isCompStart_of_rotWord_of_le lam 1 hclosedW hcW hstart (by omega)
    have hmem : (vertex (vertex (1 : G) (p ++ q ++ r ++ revWord s)
          (p.length + q.length))
        (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length))
        (p.length + q.length + r.length + (s.length - l)
          - (p.length + q.length)))⁻¹ *
        vertex (vertex (1 : G) (p ++ q ++ r ++ revWord s)
            (p.length + q.length))
          (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length)) t
        ∈ D.fam lam := hconnt
    rw [hvSw, hvo] at hmem
    exact hother o (by omega) hostart hmem
  -- the gap through the basepoint, in the rotated reading
  have happ2 := hC 4 (by omega)
    (vertex (1 : G) (p ++ q ++ r ++ revWord s) (p.length + q.length))
    (rotWord (p ++ q ++ r ++ revWord s) (p.length + q.length)) hpoly₂ lam
    (p.length + q.length + r.length + (s.length - l) - (p.length + q.length))
    (p.length + q.length + r.length + (s.length - j) - (p.length + q.length))
    ((p ++ q ++ r ++ revWord s).length - (p.length + q.length)
      + (p.length + i))
    ((p ++ q ++ r ++ revWord s).length - (p.length + q.length)
      + (p.length + k))
    hrotS hrotQ (by omega) hconn₂ hinner₂
  have hflip2 := connector_inv_mem_relBall D lam hsymm happ2
  rw [hvE, hvQ] at hflip2
  exact ⟨_, _, hflip2, hflip1, block_span_conj p q s i k j l⟩

end OsinComponents
end GGT
end GroupApproximation
