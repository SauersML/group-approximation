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


/-! ## Component starts, from the rotated word back to the word -/

/-- **Every component start of the rotated word, other than the seam's own, is a
component start of `w` at the corresponding index.**

This is `DGOIsolatedComponentRotate.exists_isCompStart_of_rotWord` with two
changes, and it should replace it: its hypothesis `IsComp lam w i k` --- a
component AT the rotation point --- is used in that proof for nothing but
`i ≤ w.length`, which is all that is assumed here; and the conclusion keeps the
branch, so a caller learns WHERE the index came from and can place it in an arc.
Without that the correspondence is unusable for anything but isolation, where
every index is equally forbidden.

The proof is fp-geometry's, unchanged: before the seam the correspondence is
`j ↦ i + j` and the previous letter is the previous letter; after it,
`j ↦ j - (|w| - i)`; and at the seam itself the index is `0` of `w`, which
starts a component because nothing precedes it. -/
theorem exists_isCompStart_of_rotWord_of_length_le (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hclosed : RelLetter.listVal w = 1) {i : ℕ}
    (hi : i ≤ w.length) {j : ℕ} (hjstart : IsCompStart lam (rotWord w i) j)
    (hj0 : j ≠ 0) :
    ∃ o : ℕ, IsCompStart lam w o ∧
      ((j < w.length - i ∧ o = i + j)
        ∨ (w.length - i ≤ j ∧ o = j - (w.length - i))) ∧
      vertex (vertex v w i) (rotWord w i) j = vertex v w o := by
  have hlen : (rotWord w i).length = w.length := length_rotWord w hi
  obtain ⟨j2, hj2⟩ := hjstart
  have hj12 : j < j2 := hj2.1
  have hj2len : j2 ≤ (rotWord w i).length := hj2.2.1
  have hjrange := hj2.2.2.1
  have hjprev := hj2.2.2.2.1
  have hjlen : j < (rotWord w i).length := by omega
  have hcj := hjrange j le_rfl hj12 hjlen
  have hj1len : j - 1 < (rotWord w i).length := by omega
  have hprevn := hjprev (j - 1) (by omega) hj1len
  rcases Nat.lt_or_ge j (w.length - i) with hlt | hge
  · rw [getElem_rotWord_lt w hi j (i + j) rfl hlt hjlen (by omega)] at hcj
    refine ⟨i + j, ?_, Or.inl ⟨hlt, rfl⟩,
      vertex_rotWord_le v w hi j (by omega)⟩
    obtain ⟨i₀, k₀, hi₀le, hjk₀, hcomp₀⟩ :=
      exists_isComp_of_isCompOf lam w (i + j) (by omega) hcj
    have hi₀ : i₀ = i + j := by
      by_contra hne
      have hprevw := hcomp₀.2.2.1 (i + (j - 1)) (by omega) (by omega) (by omega)
      rw [getElem_rotWord_lt w hi (j - 1) (i + (j - 1)) rfl (by omega) hj1len
        (by omega)] at hprevn
      exact hprevn hprevw
    exact ⟨k₀, by rw [← hi₀]; exact hcomp₀⟩
  · have hjr : j = w.length - i + (j - (w.length - i)) := by omega
    have hrlt : j - (w.length - i) < i := by omega
    rw [getElem_rotWord_add w hi j (j - (w.length - i)) hjr hrlt hjlen
      (by omega)] at hcj
    refine ⟨j - (w.length - i), ?_, Or.inr ⟨hge, rfl⟩,
      vertex_rotWord_add v w hi hclosed j (j - (w.length - i)) hjr (by omega)⟩
    obtain ⟨i₀, k₀, hi₀le, hjk₀, hcomp₀⟩ :=
      exists_isComp_of_isCompOf lam w (j - (w.length - i)) (by omega) hcj
    have hi₀ : i₀ = j - (w.length - i) := by
      rcases Nat.eq_zero_or_pos (j - (w.length - i)) with h0 | hpos
      · omega
      · by_contra hne
        have hprevw := hcomp₀.2.2.1 (j - (w.length - i) - 1) (by omega)
          (by omega) (by omega)
        rw [getElem_rotWord_add w hi (j - 1) (j - (w.length - i) - 1) (by omega)
          (by omega) hj1len (by omega)] at hprevn
        exact hprevn hprevw
    exact ⟨k₀, by rw [← hi₀]; exact hcomp₀⟩

end OsinComponents
end GGT
end GroupApproximation
