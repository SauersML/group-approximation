import GroupApproximation.GGT.OsinTheorem54SepSideLocation
import GroupApproximation.GGT.OsinTheorem54SepFourGonOpposite

/-!
# Spans are basepoint-free, and the fourth block reads backwards

Two gaps left over from the side-location layer, both needed by Lemma 4.5,
whose polygon is read from `f` rather than from `1` and whose case analysis has
to reach the reversed block.

* A component's SPAN does not depend on the basepoint: translating the path
  translates both endpoints and cancels.  `sepSet` is stated at `f` and the
  polygon lemmas at `1`, and this is what lets the two meet without moving
  either.
* A component of the polygon lying inside the fourth block is a component of
  `revWord s` --- and hence, through `isComp_revWord`, of `s` with the
  maximality clauses exchanged.  This is the backward transfer for the one
  block the side-location layer did not cover.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A span does not see the basepoint.** -/
theorem span_eq_span_one (ws : List (RelLetter G Λ)) (v : G) (i k : ℕ) :
    (vertex v ws i)⁻¹ * vertex v ws k
      = (vertex (1 : G) ws i)⁻¹ * vertex (1 : G) ws k := by
  rw [vertex_eq_mul_vertex_one ws v i, vertex_eq_mul_vertex_one ws v k]
  group

/-- **The span of a component of the side `q`, read in the polygon from any
basepoint.**  The landed `span_fourGon_side` is this at `v = 1`. -/
theorem span_fourGon_side_of_basepoint (p q r s : List (RelLetter G Λ)) (v : G)
    {i k : ℕ} (hi : i ≤ q.length) (hk : k ≤ q.length) :
    (vertex v (p ++ q ++ r ++ revWord s) (p.length + i))⁻¹ *
        vertex v (p ++ q ++ r ++ revWord s) (p.length + k)
      = (vertex (1 : G) q i)⁻¹ * vertex (1 : G) q k := by
  rw [vertex_fourGon_side p q r s v hi, vertex_fourGon_side p q r s v hk]
  group

/-- **A component of the quadrilateral inside the reversed fourth block is a
component of `revWord s`.**  The backward transfer the side-location layer left
out. -/
theorem isComp_side_revs_of_isComp_fourGon (p q r s : List (RelLetter G Λ))
    (lam : Λ) {a b : ℕ}
    (hcomp : IsComp lam (p ++ q ++ r ++ revWord s) a b)
    (ha : p.length + q.length + r.length ≤ a)
    (hb : b ≤ p.length + q.length + r.length + s.length) :
    IsComp lam (revWord s) (a - (p.length + q.length + r.length))
      (b - (p.length + q.length + r.length)) := by
  have hab := hcomp.1
  have hrange := hcomp.2.2.1
  have hpre := hcomp.2.2.2.1
  have hpost := hcomp.2.2.2.2
  have hlen : (p ++ q ++ r ++ revWord s).length
      = p.length + q.length + r.length + s.length := length_fourGon p q r s
  have hrl : (revWord s).length = s.length := length_revWord s
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2 hj
    have hn : p.length + q.length + r.length + j
        < (p ++ q ++ r ++ revWord s).length := by omega
    rw [← getElem_fourGon_revs p q r s hj rfl hn]
    exact hrange (p.length + q.length + r.length + j) (by omega) (by omega) hn
  · intro j hji hj hc
    have hn : a - 1 < (p ++ q ++ r ++ revWord s).length := by omega
    rw [← getElem_fourGon_revs p q r s hj (by omega) hn] at hc
    exact hpre (a - 1) (by omega) hn hc
  · intro hk hc
    have hn : b < (p ++ q ++ r ++ revWord s).length := by omega
    rw [← getElem_fourGon_revs p q r s hk (by omega) hn] at hc
    exact hpost hn hc

end OsinComponents
end GGT
end GroupApproximation
