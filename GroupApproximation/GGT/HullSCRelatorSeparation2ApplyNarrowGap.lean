import GroupApproximation.GGT.DGOPolygonBaseCaseTower
import GroupApproximation.GGT.OsinTheorem54SepTwoBlockRot

/-!
# The gap side, from four-point hyperbolicity

`GGT.OsinComponents.two_block_conj_named` --- the primary, in
`GGT/OsinTheorem54SepTwoBlockRot.lean` --- never touches its `hbound`: it hands
it straight to `DGOIsolatedComponentCut.connector_mem_relBall`, and the
`obtain … := hbound mu b hmu hb` happens there.  So narrowing IT to one pair of
constants narrows nothing.  What narrows the gap side is taking the cut's
CONCLUSION at one pair instead of the bound that produces it.

That is all this file does.  `two_block_conj_named_hyp` is the primary's
statement at `(1, bn)` with the same proof, opened not by `obtain … := hbound`
but by `connector_mem_relBall_at` at that one pair, whose own hypothesis
fp-geometry's tower proves from `hδ` --- four-point hyperbolicity of the
RELATIVE Cayley graph `Γ(G, X ⊔ ℋ)`.  The gap side therefore stands on `hδ`
exactly as the match side does, and carries no bound at all.

A transcription of the narrowed statement used to live here as
`two_block_conj_named_at`.  It had one consumer, the theorem below, and is gone;
its proof is now that theorem's.

**Why not the `mu = 1` convenience.**  `connector_mem_relBall_one` takes its
bound in the form `∀ b : ℝ, 0 ≤ b → …`, quantified over every REAL `b`.  The
tower proves the bound at natural `b` only, so that form is not available here,
and the `_at` spelling at the single pair `(1, (bn : ℝ))` is the one that fits.

**What is still not available, and is not wanted.**  The `∀`-form over `mu`
cannot be recovered from the tower: a `(mu, b)`-quasi-geodesic polygon at
`mu > 1` is a WEAKER object than a `(1, b')`-quasi-geodesic one for any fixed
`b'`, the defect `(y - x)(1 - 1/mu)` growing without bound along a side.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The two-block conjugation from four-point hyperbolicity alone.**  The
innermost-cut bound is no longer a hypothesis: `connector_mem_relBall_at` takes
the isolated-component bound at the pair `(1, bn)`, which fp-geometry's tower
proves from `hδ` --- four-point hyperbolicity of the RELATIVE Cayley graph
`Γ(G, X ⊔ ℋ)` --- so the gap side of the chain now stands on `hδ` exactly as
the match side does. -/
theorem two_block_conj_named_hyp (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (bn : ℕ)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
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
          ((y - x : ℕ) : ℝ) / 1 - (bn : ℝ)
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
  obtain ⟨C, hCpos, hC⟩ :=
    connector_mem_relBall_at D 1 (bn : ℝ) le_rfl (Nat.cast_nonneg bn)
      ⟨15 * (25 * (δ + bn + 1)), by omega,
        isolatedComponentBound_of_fourPointHyperbolic_at D hsymm bn hδ⟩
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
