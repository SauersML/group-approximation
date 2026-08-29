import GroupApproximation.GGT.DGOIsolatedComponentRotate

/-!
# Components away from the rotation point survive a rotation

`DGOIsolatedComponentRotate.isComp_rotWord` carries the component AT the
rotation point to index `0` of the rotated word.  A consumer that rotates in
order to see two OTHER components --- one on each side of the rotation point ---
needs a different transfer, and gets it for less: both components lie strictly
away from the rotation point, so the two maximality clauses of `IsComp` are
inherited letter for letter, through `getElem_rotWord_lt` and
`getElem_rotWord_add`.

## The seam

Only one end of one component can meet the seam, and it is the same
configuration `isComp_rotWord` has to exclude: a run reaching the END of the
word continues, in the rotated word, into whatever begins at the basepoint.  So
the transfer after the rotation point carries `hwrap` --- fp-geometry's
hypothesis, in fp-geometry's shape --- and `notIsCompOf_fourGon_zero` discharges
it for a quadrilateral whose first side is spelled by base letters and is
nonempty, which is the case a caller meets.

Before the rotation point no such hypothesis is needed at the far end: a
component ending exactly at the rotation point ends the rotated word, where the
maximality clause is vacuous.  What is needed there is that the component does
not start at the basepoint, for the mirror-image reason.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

omit [Group G] in
/-- **A component starting strictly after the rotation point is a component of
the rotated word**, at indices shifted down by it. -/
theorem isComp_rotWord_after (lam : Λ) {w : List (RelLetter G Λ)} {i a k : ℕ}
    (hi : i ≤ w.length) (hcomp : IsComp lam w a k) (hia : i < a)
    (hwrap : ∀ h0 : 0 < w.length, k = w.length → ¬ (w[0]'h0).IsCompOf lam) :
    IsComp lam (rotWord w i) (a - i) (k - i) := by
  have hak : a < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have hrange := hcomp.2.2.1
  have hpre := hcomp.2.2.2.1
  have hpost := hcomp.2.2.2.2
  have hlen : (rotWord w i).length = w.length := length_rotWord w hi
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2 hj
    rw [getElem_rotWord_lt w hi j (i + j) rfl (by omega) hj (by omega)]
    exact hrange (i + j) (by omega) (by omega) (by omega)
  · intro j hj hjlen hc
    rw [getElem_rotWord_lt w hi j (a - 1) (by omega) (by omega) hjlen
      (by omega)] at hc
    exact hpre (a - 1) (by omega) (by omega) hc
  · intro hk hc
    rcases Nat.lt_or_ge (k - i) (w.length - i) with hlt | hge
    · rw [getElem_rotWord_lt w hi (k - i) k (by omega) hlt hk (by omega)] at hc
      exact hpost (by omega) hc
    · have hkk : k = w.length := by omega
      rw [getElem_rotWord_add w hi (k - i) 0 (by omega) (by omega) hk
        (by omega)] at hc
      exact hwrap (by omega) hkk hc

omit [Group G] in
/-- **A component ending at or before the rotation point, and not starting at
the basepoint, is a component of the rotated word**, at indices shifted up past
the seam. -/
theorem isComp_rotWord_before (lam : Λ) {w : List (RelLetter G Λ)} {i a k : ℕ}
    (hi : i ≤ w.length) (hcomp : IsComp lam w a k) (hki : k ≤ i)
    (hstart : 0 < a) :
    IsComp lam (rotWord w i) (w.length - i + a) (w.length - i + k) := by
  have hak : a < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have hrange := hcomp.2.2.1
  have hpre := hcomp.2.2.2.1
  have hpost := hcomp.2.2.2.2
  have hlen : (rotWord w i).length = w.length := length_rotWord w hi
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2 hj
    rw [getElem_rotWord_add w hi j (j - (w.length - i)) (by omega) (by omega) hj
      (by omega)]
    exact hrange (j - (w.length - i)) (by omega) (by omega) (by omega)
  · intro j hj hjlen hc
    rw [getElem_rotWord_add w hi j (a - 1) (by omega) (by omega) hjlen
      (by omega)] at hc
    exact hpre (a - 1) (by omega) (by omega) hc
  · intro hk hc
    have hklt : k < i := by omega
    rw [getElem_rotWord_add w hi (w.length - i + k) k (by omega) hklt hk
      (by omega)] at hc
    exact hpost (by omega) hc

/-- **The quadrilateral's first letter is a base letter**, so nothing wraps into
it.  This is `hwrap` for `p ++ q ++ r ++ revWord s`, whenever the first short
side is nonempty. -/
theorem notIsCompOf_fourGon_zero (p q r s : List (RelLetter G Λ)) (lam : Λ)
    (hp : ∀ a ∈ p, ∃ x : G, a = RelLetter.base x) (hp0 : 0 < p.length)
    (h0 : 0 < (p ++ q ++ r ++ revWord s).length) :
    ¬ ((p ++ q ++ r ++ revWord s)[0]'h0).IsCompOf lam := by
  intro hc
  obtain ⟨x, hx⟩ := hp _ (getElem_mem_fourGon_p p q r s hp0 h0)
  rw [hx] at hc
  exact hc

end OsinComponents
end GGT
end GroupApproximation
