import GroupApproximation.GGT.OsinTheorem54SepFourGonSide

/-!
# Which side a component lives on

The quadrilateral machinery so far runs one way --- a component of a long side
becomes a component of the polygon --- and it pays for the two block boundaries
with the hypothesis that the SHORT sides are spelled by base letters, which is
what keeps a run from continuing across them.

Osin's Lemma 4.9 is about a geodesic triangle, where every side carries whatever
letters the geodesic has, so that hypothesis is unavailable and the transfer has
to be stated symmetrically.  Two facts replace it.

* Forward, without any hypothesis on `r`: a component of `q` that does not reach
  the END of `q` is a component of the polygon.  The `r`-hypothesis was only
  ever used at `k = |q|`, where the run can continue into the next block; below
  that, maximality is inherited from `q` itself, and at the front `i = 0` needs
  nothing because index `0` of the polygon has no predecessor.
* Backward, on each long block: a component of the polygon whose run lies inside
  one block is a component of that block's side.  This direction is free ---
  maximality in the longer word implies it in the shorter, and where the block
  boundary cuts, the side's own clause is vacuous.

Together they locate a component: a run of the polygon that meets the `q`-block
without leaving it comes from `q`, and one that meets the `r`-block without
leaving it comes from `r`.  The runs that DO leave a block are the corner cases,
there is at most one at each corner, and that is where Lemma 4.9's defect will
come from.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A letter of the quadrilateral in the `r`-block is a letter of `r`**, at
the index named by an equation. -/
theorem getElem_fourGon_r (p q r s : List (RelLetter G Λ)) {n j : ℕ}
    (hj : j < r.length) (hnj : n = p.length + q.length + j)
    (hn : n < (p ++ q ++ r ++ revWord s).length) :
    (p ++ q ++ r ++ revWord s)[n]'hn = r[j]'hj := by
  subst hnj
  have h1 : p.length + q.length + j < (p ++ q ++ r).length := by
    rw [List.length_append, List.length_append]
    omega
  have h4 : (p ++ q).length ≤ p.length + q.length + j := by
    rw [List.length_append]
    omega
  rw [List.getElem_append_left h1, List.getElem_append_right h4]
  refine getElem_congr_idx ?_
  rw [List.length_append]
  omega

/-- **A component of `q` that stops short of the end of `q` is a component of
the quadrilateral**, with no hypothesis on the third side. -/
theorem isComp_fourGon_of_isComp_side_of_lt (p q r s : List (RelLetter G Λ))
    (lam : Λ) (hp : ∀ a ∈ p, ∃ x : G, a = RelLetter.base x) {i k : ℕ}
    (hcomp : IsComp lam q i k) (hk : k < q.length) :
    IsComp lam (p ++ q ++ r ++ revWord s) (p.length + i) (p.length + k) := by
  obtain ⟨hik, hkq, hrange, hpre, hpost⟩ := hcomp
  have hlen : (p ++ q ++ r ++ revWord s).length
      = p.length + q.length + r.length + s.length := length_fourGon p q r s
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
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
  · intro hkl hc
    rw [getElem_fourGon_q p q r s hk rfl hkl] at hc
    exact hpost hk hc

/-- **A component of the quadrilateral inside the `q`-block is a component of
`q`.**  No hypothesis at all: this direction only loses information. -/
theorem isComp_side_q_of_isComp_fourGon (p q r s : List (RelLetter G Λ))
    (lam : Λ) {a b : ℕ}
    (hcomp : IsComp lam (p ++ q ++ r ++ revWord s) a b)
    (ha : p.length ≤ a) (hb : b ≤ p.length + q.length) :
    IsComp lam q (a - p.length) (b - p.length) := by
  have hab := hcomp.1
  have hrange := hcomp.2.2.1
  have hpre := hcomp.2.2.2.1
  have hpost := hcomp.2.2.2.2
  have hlen : (p ++ q ++ r ++ revWord s).length
      = p.length + q.length + r.length + s.length := length_fourGon p q r s
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2 hj
    have hn : p.length + j < (p ++ q ++ r ++ revWord s).length := by omega
    rw [← getElem_fourGon_q p q r s hj rfl hn]
    exact hrange (p.length + j) (by omega) (by omega) hn
  · intro j hji hj hc
    have hn : a - 1 < (p ++ q ++ r ++ revWord s).length := by omega
    rw [← getElem_fourGon_q p q r s hj (by omega) hn] at hc
    exact hpre (a - 1) (by omega) hn hc
  · intro hk hc
    have hn : b < (p ++ q ++ r ++ revWord s).length := by omega
    rw [← getElem_fourGon_q p q r s hk (by omega) hn] at hc
    exact hpost hn hc

/-- **A component of the quadrilateral inside the `r`-block is a component of
`r`.**  The same, one block along. -/
theorem isComp_side_r_of_isComp_fourGon (p q r s : List (RelLetter G Λ))
    (lam : Λ) {a b : ℕ}
    (hcomp : IsComp lam (p ++ q ++ r ++ revWord s) a b)
    (ha : p.length + q.length ≤ a) (hb : b ≤ p.length + q.length + r.length) :
    IsComp lam r (a - (p.length + q.length)) (b - (p.length + q.length)) := by
  have hab := hcomp.1
  have hrange := hcomp.2.2.1
  have hpre := hcomp.2.2.2.1
  have hpost := hcomp.2.2.2.2
  have hlen : (p ++ q ++ r ++ revWord s).length
      = p.length + q.length + r.length + s.length := length_fourGon p q r s
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2 hj
    have hn : p.length + q.length + j
        < (p ++ q ++ r ++ revWord s).length := by omega
    rw [← getElem_fourGon_r p q r s hj rfl hn]
    exact hrange (p.length + q.length + j) (by omega) (by omega) hn
  · intro j hji hj hc
    have hn : a - 1 < (p ++ q ++ r ++ revWord s).length := by omega
    rw [← getElem_fourGon_r p q r s hj (by omega) hn] at hc
    exact hpre (a - 1) (by omega) hn hc
  · intro hk hc
    have hn : b < (p ++ q ++ r ++ revWord s).length := by omega
    rw [← getElem_fourGon_r p q r s hk (by omega) hn] at hc
    exact hpost hn hc

end OsinComponents
end GGT
end GroupApproximation
