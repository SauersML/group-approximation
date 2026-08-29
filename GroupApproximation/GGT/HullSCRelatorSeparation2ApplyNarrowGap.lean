import GroupApproximation.GGT.OsinTheorem54SepTwoBlockRot

/-!
# The gap side, narrowed at its own hypothesis

`GGT.OsinComponents.two_block_conj_named` never touches its `hbound`: it hands
it straight to `DGOIsolatedComponentCut.connector_mem_relBall`, and the
`obtain … := hbound mu b hmu hb` happens there.  So narrowing IT to one pair of
constants does not narrow this theorem --- what narrows this theorem is taking
the cut's CONCLUSION at one pair instead of the bound that produces it.

`two_block_conj_named_at` is that: the same statement and the same proof, with
the call to `connector_mem_relBall` replaced by the hypothesis it would have
returned.  `hmu` and `hb` disappear, having existed only to feed that call.

## What this buys, and what it does not

It buys the narrowest honest binder on the gap side: instead of the
isolated-component bound at EVERY real pair `(mu, b)`, the innermost-cut bound
at the one pair the chain uses.  That is strictly closer to what fp-geometry's
tower proves, and it is the form a narrowed `connector_mem_relBall` would
discharge outright.

It does not reach a discharge.  Getting from the tower to the cut's conclusion
means narrowing `connector_mem_relBall` itself, whose proof is some two hundred
and fifty lines, and the `∀`-form cannot be recovered from the tower: a
`(mu, b)`-quasi-geodesic polygon at `mu > 1` is a WEAKER object than a
`(1, b')`-quasi-geodesic one for any fixed `b'`, the defect `(y - x)(1 - 1/mu)`
growing without bound along a side, so no choice of `b'` and no cast reaches it.
The gap side therefore still carries a hypothesis; it is now the smallest one
the chain can be stated against.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Both gaps of a matched pair are short, from the cut at one pair of
constants.**

`GGT.OsinComponents.two_block_conj_named` with its hypothesis narrowed from the
isolated-component bound at every `(mu, b)` to the innermost-cut bound at this
one; the proof is unchanged below its first line. -/
theorem two_block_conj_named_at (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (mu b : ℝ)
    (hcut : ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 5 → ∀ (v : G) (w : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v w →
        ∀ (lam : Λ) (i k i' k' : ℕ), IsComp lam w i k → IsComp lam w i' k' →
          i < i' → Connected D.fam lam v w i i' →
          (∀ p : ℕ, i < p → p < i' → IsCompStart lam w p →
            ¬ Connected D.fam lam v w i p) →
          (vertex v w i')⁻¹ * vertex v w k ∈ D.relBall lam (C * n)) :
    ∃ C : ℕ, 0 < C ∧
      ∀ (lam : Λ) (p q r s : List (RelLetter G Λ)) (i k j l : ℕ),
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
        ((vertex (1 : G) s j)⁻¹ * (RelLetter.listVal p * vertex (1 : G) q i)
            ∈ D.relBall lam (C * 4)) ∧
          ((RelLetter.listVal p * vertex (1 : G) q k)⁻¹ * vertex (1 : G) s l
            ∈ D.relBall lam (C * 4)) := by
  obtain ⟨C, hCpos, hC⟩ := hcut
  refine ⟨C, hCpos, ?_⟩
  intro lam p q r s i k j l hclose hlet hp hr hp0 hqg hcompq hkq hcomps hlq
    hconn hinner hother
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
  have hbridgeq := isComp_fourGon_of_isComp_side p q r s lam hp hr hcompq hkq
  have hbridges := isComp_fourGon_of_isComp_opposite p q r s lam hr hcomps hlq
  have hwrap : ∀ h0 : 0 < (p ++ q ++ r ++ revWord s).length,
      p.length + q.length + r.length + (s.length - j)
        = (p ++ q ++ r ++ revWord s).length →
      ¬ ((p ++ q ++ r ++ revWord s)[0]'h0).IsCompOf lam :=
    fun h0 _ => notIsCompOf_fourGon_zero p q r s lam hp hp0 h0
  have hrotS := isComp_rotWord_after lam hcW hbridges (by omega) hwrap
  have hrotQ := isComp_rotWord_before lam hcW hbridgeq (by omega) (by omega)
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
  have happ1 := hC 4 (by omega) 1 (p ++ q ++ r ++ revWord s) hpoly lam
    (p.length + i) (p.length + k)
    (p.length + q.length + r.length + (s.length - l))
    (p.length + q.length + r.length + (s.length - j))
    hbridgeq hbridges (by omega) hconn hinner
  have hflip1 := connector_inv_mem_relBall D lam hsymm happ1
  rw [vertex_fourGon_side p q r s 1 hkle, one_mul,
    vertex_fourGon_opposite_closed p q r s hclose l] at hflip1
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
      exists_isCompStart_of_rotWord_of_length_le lam 1 hclosedW hcW hstart
        (by omega)
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
  exact ⟨hflip2, hflip1⟩

end OsinComponents
end GGT
end GroupApproximation
