import GroupApproximation.GGT.OsinTheorem54SepTwoBlockRot

/-!
# The two gaps, named

`GGT.OsinComponents.exists_two_block_conj_of_rot` bounds both gaps of a matched
pair of blocks and then hides them behind an existential.  What its proof
establishes is stronger, and the applications need the stronger form: the two
elements it puts in the relative ball are the polygon's OWN gaps,

* `x  = (vertex 1 s j)⁻¹ * (listVal p * vertex 1 q i)`,
* `x' = (listVal p * vertex 1 q k)⁻¹ * vertex 1 s l`,

named exactly as `GGT.OsinComponents.exists_block_span_conj` names them.

The naming is not decoration.  The aligned branch of Olshanskii's step (c)
spends it and not the identity: `HullSC.listVal_conj_of_alignedTrivial` consumes
the VERTEX relation `y * vertex 1 w i = vertex 1 w' j`, and that relation is
what `x = 1` says once `x` is known to be the first gap.  From
`∃ x x', x * v_q * x' = v_s` alone the design's clauses still give `x = 1` and
`x' = 1`, so they still give `e = f`; but `x` is then some element of the ball
about which nothing further is known, and the vertex relation does not follow.
So the aligned and mirrored cases need the gaps by name, and the two mixed cases
do not.

`two_block_conj_mem_relBall` is the same theorem with the same proof and the
named conclusion.  One further change: the index of the family is quantified
INSIDE the existential over the constant rather than outside it.  That costs
nothing --- the constant comes from `connector_mem_relBall`, which is uniform in
the index --- and it saves a caller over a family indexed by `Bool` from taking
a maximum of two constants and weakening both balls to it.

Two vacuity lemmas come with it.  Both are about a quadrilateral whose two short
sides are base-spelled: no component starts inside the first side, and none
inside the third.  They discharge the two configuration clauses of the packaged
theorem in the configuration the relator chain builds, where the two long sides
are single block letters and the two short ones are the connectors.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Two base-spelled sides carry no component start -/

/-- **No component of the quadrilateral starts inside a base-spelled first
side.**  A base letter carries no index, so it is not a component letter, and
the letter at a component's start always is one. -/
theorem not_isCompStart_fourGon_p (p q r s : List (RelLetter G Λ)) (lam : Λ)
    (hp : ∀ a ∈ p, ∃ x : G, a = RelLetter.base x) {o : ℕ} (ho : o < p.length) :
    ¬ IsCompStart lam (p ++ q ++ r ++ revWord s) o := by
  rintro ⟨k, hcomp⟩
  have hov : o < (p ++ q ++ r ++ revWord s).length := by
    rw [length_fourGon]
    omega
  have hc := hcomp.2.2.1 o le_rfl hcomp.1 hov
  obtain ⟨x, hx⟩ := hp _ (getElem_mem_fourGon_p p q r s ho hov)
  rw [hx] at hc
  exact hc

/-- **No component of the quadrilateral starts inside a base-spelled third
side.**  This is the innermost clause of the first reading, in the
configuration where the two long sides are single letters: the range the clause
quantifies over is exactly the third side. -/
theorem not_isCompStart_fourGon_r (p q r s : List (RelLetter G Λ)) (lam : Λ)
    (hr : ∀ a ∈ r, ∃ x : G, a = RelLetter.base x) {o : ℕ}
    (h1 : p.length + q.length ≤ o) (h2 : o < p.length + q.length + r.length) :
    ¬ IsCompStart lam (p ++ q ++ r ++ revWord s) o := by
  rintro ⟨k, hcomp⟩
  have hov : o < (p ++ q ++ r ++ revWord s).length := by
    rw [length_fourGon]
    omega
  have hc := hcomp.2.2.1 o le_rfl hcomp.1 hov
  obtain ⟨x, hx⟩ := hr _ (getElem_mem_fourGon_r p q r s h1 h2 hov)
  rw [hx] at hc
  exact hc

/-! ## The packaged theorem, with its gaps named -/

/-- **Both gaps of a matched pair of blocks are short, and they are the
polygon's own gaps.**

Every hypothesis is `GGT.OsinComponents.exists_two_block_conj_of_rot`'s, and so
is the proof: the direct reading of the quadrilateral bounds the gap from the
end of the `q`-component to the start of the `s`-component, the reading from the
corner between `q` and `r` bounds the gap through the basepoint, and
`connector_inv_mem_relBall` puts each the right way round.  What changes is the
conclusion, which keeps the two elements rather than existentially quantifying
them, and the position of the family index, which is now inside. -/
theorem two_block_conj_mem_relBall (D : RelGenSet G Λ)
    (hbound : ∀ mu b : ℝ, 1 ≤ mu → 0 ≤ b → ∃ C : ℕ, 0 < C ∧
      ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
        IsQuasiGeodesicPolygon D mu b n v u →
        ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
          (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (mu b : ℝ) (hmu : 1 ≤ mu)
    (hb : 0 ≤ b) :
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
  obtain ⟨C, hCpos, hC⟩ := connector_mem_relBall D hbound mu b hmu hb
  refine ⟨C, hCpos, ?_⟩
  intro lam p q r s i k j l hclose hlet hp hr hp0 hqg hcompq hkq hcomps hlq
    hconn hinner hother
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
  exact ⟨hflip2, hflip1⟩

end OsinComponents
end GGT
end GroupApproximation
