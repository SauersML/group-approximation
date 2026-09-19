import GroupApproximation.GGT.OsinTheorem54SepSideLocation
import GroupApproximation.GGT.OsinTheorem54SepFourGonSpan

/-!
# Two bridges for Lemma 4.5's case analysis

Both are small, and both exist because 4.5 reads its polygon from `f` --- where
`sepSet` lives --- while the side transfers were written at the basepoint `1`
and with the corner excluded by an index bound.

* `isComp_fourGon_of_isComp_side_of_post` takes post-maximality in the POLYGON
  as a hypothesis instead of deriving it from `k < |q|`.  4.5 case-splits on
  exactly that clause: when it holds the component transfers and the isolation
  argument runs; when it fails the run continues past the corner, which is the
  branch `OsinTheorem54SepCorner45` handles.  The landed
  `isComp_fourGon_of_isComp_side_of_lt` is this with the clause discharged.
* `vertex_fourGon_opposite_closed_of_basepoint` is the fourth block's vertex
  identification at an arbitrary basepoint; the landed version is the case
  `v = 1`.  A match landing in the reversed block is read back onto its side
  through it.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The side-to-polygon transfer, with post-maximality assumed.** -/
theorem isComp_fourGon_of_isComp_side_of_post (p q r s : List (RelLetter G Λ))
    (lam : Λ) (hp : ∀ a ∈ p, ∃ x : G, a = RelLetter.base x) {i k : ℕ}
    (hcomp : IsComp lam q i k)
    (hpost : ∀ hkl : p.length + k < (p ++ q ++ r ++ revWord s).length,
      ¬ ((p ++ q ++ r ++ revWord s)[p.length + k]'hkl).IsCompOf lam) :
    IsComp lam (p ++ q ++ r ++ revWord s) (p.length + i) (p.length + k) := by
  obtain ⟨hik, hkq, hrange, hpre, -⟩ := hcomp
  have hlen : (p ++ q ++ r ++ revWord s).length
      = p.length + q.length + r.length + s.length := length_fourGon p q r s
  refine ⟨by omega, by omega, ?_, ?_, hpost⟩
  · intro j hj1 hj2 hj
    have hj' : j - p.length < q.length := by omega
    rw [getElem_fourGon_q p q r s hj' (by omega) hj]
    exact hrange (j - p.length) (by omega) (by omega) hj'
  · intro j hji hj hc
    by_cases hi0 : 0 < i
    · have hj' : i - 1 < q.length := by omega
      rw [getElem_fourGon_q p q r s hj' (by omega) hj] at hc
      exact hpre (i - 1) (by omega) hj' hc
    · have hjp : j < p.length := by omega
      obtain ⟨x, hx⟩ := hp _ (getElem_mem_fourGon_p p q r s hjp hj)
      rw [hx] at hc
      exact hc

/-- **The fourth block's vertex, from any basepoint.**  The landed
`vertex_fourGon_opposite_closed` is `v = 1`; the closing relation cancels the
translation the same way. -/
theorem vertex_fourGon_opposite_closed_of_basepoint
    (p q r s : List (RelLetter G Λ)) (v : G)
    (hclose : RelLetter.listVal s
      = RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r)
    (j : ℕ) :
    vertex v (p ++ q ++ r ++ revWord s)
        (p.length + q.length + r.length + (s.length - j))
      = v * vertex (1 : G) s j := by
  rw [vertex_fourGon_opposite p q r s v j]
  have h : v * RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r
      = v * RelLetter.listVal s := by
    rw [hclose]
    group
  rw [h]
  group

end OsinComponents
end GGT
end GroupApproximation
