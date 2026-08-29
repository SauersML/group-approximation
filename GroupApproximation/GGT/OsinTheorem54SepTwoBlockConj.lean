import GroupApproximation.GGT.DGOIsolatedComponentCut
import GroupApproximation.GGT.OsinTheorem54SepBlockConj
import GroupApproximation.GGT.OsinTheorem54SepFourGonOpposite

/-!
# Two matched blocks, with both gaps bounded

The packaged form of `x * v_q * x' = v_s`: two components of a quadrilateral,
one on each long side, matched to each other, with BOTH connecting elements in a
relative ball of radius `4C`.

`GGT/OsinTheorem54SepBlockConj.lean` supplies the identity and says nothing
about the size of `x` and `x'`; the bound on each comes from one application of
the innermost end-to-start cut, `DGOIsolatedComponentCut.connector_mem_relBall`,
flipped by `connector_inv_mem_relBall`.

## Why the polygon is assumed twice

The two gaps are the two arcs of a CYCLIC object between the same two
components, and a word is a linearisation: it cuts one of the two arcs.
Whichever arrangement of the four sides is written down, one gap runs from the
end of one component to the start of the other *inside* the word --- and the
cut bound applies to it --- while the other gap runs through the basepoint, and
no ordering of indices in that word exhibits it as an end-to-start pair.

So the second gap is bounded by re-reading the same polygon from a different
basepoint, and the hypothesis for that reading is stated abstractly: a polygon
`(v₂, u₂)` with two matched components whose relevant vertices are the two
group elements in question.  For the rotation of `p ++ q ++ r ++ revWord s`
that starts at the far end of `s`, those two identifications are computations in
the vertex calculus, and a consumer with concrete short sides discharges them
directly.

The second reading is a rotation, and it is derivable rather than fundamental.
The reading has to begin in the arc between the end of the `q`-component and the
start of the `s`-component, and that arc always contains the corner `|p| + |q|`:
the component of `q` ends at or before it, and the component of the reversed `s`
starts at or after `|p| + |q| + |r|`.  Rotation at a corner is available ---
`DGOIsolatedComponentRotateCut.exists_rot_cut`, packaged back into the predicate
by `OsinTheorem54SepRotatePolygon.isQuasiGeodesicPolygon_rotWord` --- and it
keeps the number of sides, so the rotated quadrilateral is a quadrilateral.

What is still to be written is the transfer of the two components and their
vertices into the rotated word (`isComp_rotWord`, `vertex_rotWord_le` and
`vertex_rotWord_add` are what it would run on).  Until that is done the second
reading stays a hypothesis rather than something smuggled in: the cut bound is
only ever applied to what the caller has certified is a quasi-geodesic polygon.
Its own innermost clause is genuinely new information in any case --- it is
about the component starts in the OTHER arc --- and no rotation lemma supplies
that.

## What is not claimed

Nothing bounds `v_q` or `v_s`.  They are the deep spans, unbounded by design,
and they stay between the two gaps: `block_span_conj` is the identity that keeps
them there.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Both gaps of a matched pair of blocks are short, and they conjugate one
span to the other.**

The first binder after `D` is the isolated-component bound in the `n ≤ 6` side
form --- the exact hypothesis `DGOIsolatedComponentCut.connector_mem_relBall`
consumes, since cutting an `n`-gon produces an `(n + 1)`-gon and the quadrilateral
here is cut once.  Everything else is proved.

The two conclusions `x, x' ∈ D.relBall lam (C * 4)` are at the same constant,
one per orientation. -/
theorem exists_two_block_conj_of_innermost (D : RelGenSet G Λ) (lam : Λ)
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
        (∀ a ∈ p, ∃ x : G, a = RelLetter.base x) →
        (∀ a ∈ r, ∃ x : G, a = RelLetter.base x) →
        IsQuasiGeodesicPolygon D mu b 4 1 (p ++ q ++ r ++ revWord s) →
        IsComp lam q i k → (k < q.length ∨ 0 < r.length) →
        IsComp lam s j l → (l < s.length ∨ 0 < r.length) →
        Connected D.fam lam 1 (p ++ q ++ r ++ revWord s) (p.length + i)
            (p.length + q.length + r.length + (s.length - l)) →
        (∀ t : ℕ, p.length + i < t →
          t < p.length + q.length + r.length + (s.length - l) →
          IsCompStart lam (p ++ q ++ r ++ revWord s) t →
          ¬ Connected D.fam lam 1 (p ++ q ++ r ++ revWord s)
            (p.length + i) t) →
        ∀ (v₂ : G) (u₂ : List (RelLetter G Λ)) (i₂ k₂ i₂' k₂' : ℕ),
          IsQuasiGeodesicPolygon D mu b 4 v₂ u₂ →
          IsComp lam u₂ i₂ k₂ → IsComp lam u₂ i₂' k₂' → i₂ < i₂' →
          Connected D.fam lam v₂ u₂ i₂ i₂' →
          (∀ t : ℕ, i₂ < t → t < i₂' → IsCompStart lam u₂ t →
            ¬ Connected D.fam lam v₂ u₂ i₂ t) →
          vertex v₂ u₂ k₂ = vertex (1 : G) s j →
          vertex v₂ u₂ i₂' = RelLetter.listVal p * vertex (1 : G) q i →
        ∃ x x' : G, x ∈ D.relBall lam (C * 4) ∧ x' ∈ D.relBall lam (C * 4) ∧
          x * ((vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k) * x'
            = (vertex (1 : G) s j)⁻¹ * vertex (1 : G) s l := by
  obtain ⟨C, hCpos, hC⟩ := connector_mem_relBall D hbound mu b hmu hb
  refine ⟨C, hCpos, ?_⟩
  intro p q r s i k j l hclose hp hr hpoly hcompq hkq hcomps hlq hconn hinner
    v₂ u₂ i₂ k₂ i₂' k₂' hpoly₂ hcomp₂ hcomp₂' hlt₂ hconn₂ hinner₂ hvk hvi
  have hiq : i < q.length := lt_of_lt_of_le hcompq.1 hcompq.2.1
  have hkle : k ≤ q.length := hcompq.2.1
  have hbridgeq := isComp_fourGon_of_isComp_side p q r s lam hp hr hcompq hkq
  have hbridges := isComp_fourGon_of_isComp_opposite p q r s lam hr hcomps hlq
  -- the gap from the end of the `q`-block to the start of the `s`-block
  have happ1 := hC 4 (by omega) 1 (p ++ q ++ r ++ revWord s) hpoly lam
    (p.length + i) (p.length + k)
    (p.length + q.length + r.length + (s.length - l))
    (p.length + q.length + r.length + (s.length - j))
    hbridgeq hbridges (by omega) hconn hinner
  have hflip1 := connector_inv_mem_relBall D lam hsymm happ1
  rw [vertex_fourGon_side p q r s 1 hkle, one_mul,
    vertex_fourGon_opposite_closed p q r s hclose l] at hflip1
  -- the gap through the basepoint, read in the second linearisation
  have happ2 := hC 4 (by omega) v₂ u₂ hpoly₂ lam i₂ k₂ i₂' k₂'
    hcomp₂ hcomp₂' hlt₂ hconn₂ hinner₂
  have hflip2 := connector_inv_mem_relBall D lam hsymm happ2
  rw [hvk, hvi] at hflip2
  exact ⟨_, _, hflip2, hflip1, block_span_conj p q s i k j l⟩

end OsinComponents
end GGT
end GroupApproximation
