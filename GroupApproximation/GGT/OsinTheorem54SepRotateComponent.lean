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

/-! ## Isolatedness before the rotation point -/

/-- **Isolation at the basepoint rules out a terminal `lam`-run.**

This is the other cyclic maximality fact, dual to
`notMem_wrap_of_isIsolated`.  If the last letter belonged to `H_lam`, the
component containing it would end at the closing vertex.  Closedness identifies
that vertex with the start of the distinguished component at `0`, so the two
components would be connected. -/
theorem notMem_terminal_of_isIsolated_zero (D : RelGenSet G Λ) (lam : Λ)
    (v : G) {w : List (RelLetter G Λ)}
    (hlet : ∀ x ∈ w, D.IsLetter x)
    (hclosed : RelLetter.listVal w = 1) {k : ℕ}
    (hcomp : IsComp lam w 0 k) (hiso : IsIsolated D.fam lam v w 0)
    (hklen : k < w.length) :
    ¬ (w[w.length - 1]'(by omega)).IsCompOf lam := by
  intro hlast
  obtain ⟨q, r, hqle, hltr, hqr⟩ :=
    exists_isComp_of_isCompOf lam w (w.length - 1) (by omega) hlast
  have hr : r = w.length := by omega
  have hq0 : q ≠ 0 := by
    intro hq
    subst q
    have hrk : r = k := isComp_end_unique hqr hcomp
    omega
  have hspan : (vertex v w q)⁻¹ * vertex v w r ∈ D.fam lam :=
    span_mem_fam_of_isComp D v hlet hqr
  refine hiso.2 q hq0 ⟨r, hqr⟩ ?_
  rw [hr, vertex_length_of_closed v w hclosed] at hspan
  have heq : ((vertex v w q)⁻¹ * v)⁻¹ = v⁻¹ * vertex v w q := by
    group
  rw [vertex_zero, ← heq]
  exact inv_mem hspan

omit [Group G] in
/-- **The basepoint component survives a later rotation.**

The component `[0,k)` moves to `[|w|-i, |w|-i+k)`.  Its new predecessor is
the final letter of `w`, which is why this is separate from
`isComp_rotWord_before`; `hterminal` is precisely the cyclic maximality fact
supplied by isolation and closedness above. -/
theorem isComp_rotWord_zero_before (lam : Λ) {w : List (RelLetter G Λ)}
    {i k : ℕ} (hi : i < w.length) (hcomp : IsComp lam w 0 k)
    (hki : k ≤ i)
    (hterminal : ¬ (w[w.length - 1]'(by omega)).IsCompOf lam) :
    IsComp lam (rotWord w i) (w.length - i) (w.length - i + k) := by
  have hkw : k ≤ w.length := hcomp.2.1
  have hrange := hcomp.2.2.1
  have hpost := hcomp.2.2.2.2
  have hlen : (rotWord w i).length = w.length := length_rotWord w (le_of_lt hi)
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2 hj
    rw [getElem_rotWord_add w (le_of_lt hi) j (j - (w.length - i))
      (by omega) (by omega) hj (by omega)]
    exact hrange (j - (w.length - i)) (by omega) (by omega) (by omega)
  · intro j hj hjlen hc
    rw [getElem_rotWord_lt w (le_of_lt hi) j (w.length - 1)
      (by omega) (by omega) hjlen (by omega)] at hc
    exact hterminal hc
  · intro hk hc
    have hki' : k < i := by omega
    rw [getElem_rotWord_add w (le_of_lt hi) (w.length - i + k) k rfl hki'
      hk (by omega)] at hc
    exact hpost (by omega) hc

/-- **The isolated basepoint component survives a later rotation.**

This closes the only cyclic transport case omitted by
`isIsolated_rotWord_before`: the predecessor needed after rotation is the last
letter of the original word, and `notMem_terminal_of_isIsolated_zero` rules it
out. -/
theorem isIsolated_rotWord_zero_before (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ x ∈ w, D.IsLetter x)
    (hclosed : RelLetter.listVal w = 1) {i k : ℕ} (hi : i < w.length)
    (hcomp : IsComp lam w 0 k) (hki : k ≤ i)
    (hiso : IsIsolated D.fam lam v w 0) :
    IsIsolated D.fam lam (vertex v w i) (rotWord w i) (w.length - i) := by
  have hterminal : ¬ (w[w.length - 1]'(by omega)).IsCompOf lam :=
    notMem_terminal_of_isIsolated_zero D lam v hlet hclosed hcomp hiso (by omega)
  have hrotcomp : IsComp lam (rotWord w i) (w.length - i)
      (w.length - i + k) :=
    isComp_rotWord_zero_before lam hi hcomp hki hterminal
  have hdistVertex : vertex (vertex v w i) (rotWord w i) (w.length - i) =
      vertex v w 0 := by
    exact vertex_rotWord_add v w (le_of_lt hi) hclosed (w.length - i) 0 rfl
      (by omega)
  refine ⟨⟨w.length - i + k, hrotcomp⟩, ?_⟩
  intro p hpdist hpstart hconn
  have hmem : (vertex v w 0)⁻¹ *
      vertex (vertex v w i) (rotWord w i) p ∈ D.fam lam := by
    rw [← hdistVertex]
    exact hconn
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · subst hp0
    have hv0 : vertex (vertex v w i) (rotWord w i) 0 = vertex v w i := by
      rw [vertex_rotWord_le v w (le_of_lt hi) 0 (by omega), Nat.add_zero]
    obtain ⟨p₂, hp₂⟩ := hpstart
    have hci : (w[i]'hi).IsCompOf lam := by
      have hc0 := hp₂.2.2.1 0 le_rfl hp₂.1 (by omega)
      rwa [getElem_rotWord_lt w (le_of_lt hi) 0 (i + 0) rfl (by omega)
        (by omega) (by omega)] at hc0
    obtain ⟨q, qk, hqi, hiqk, hqcomp⟩ :=
      exists_isComp_of_isCompOf lam w i hi hci
    have hq0 : q ≠ 0 := by
      intro hq
      subst q
      have hends : qk = k := isComp_end_unique hqcomp hcomp
      omega
    have hqconn : Connected D.fam lam v w q i := by
      exact span_mem_fam D lam v hlet i (by omega) q hqi
        (fun m hm1 hm2 hm3 ⇒ hqcomp.2.2.1 m hm1 (by omega) hm3)
    rw [hv0] at hmem
    refine hiso.2 q hq0 ⟨qk, hqcomp⟩ ?_
    have heq : (vertex v w 0)⁻¹ * vertex v w q =
        ((vertex v w 0)⁻¹ * vertex v w i) *
          ((vertex v w q)⁻¹ * vertex v w i)⁻¹ := by
      group
    rw [heq]
    exact mul_mem hmem (inv_mem hqconn)
  · obtain ⟨q, hqstart, hwhere, hvq⟩ :=
      exists_isCompStart_of_rotWord_of_length_le lam v hclosed (le_of_lt hi)
        hpstart (by omega)
    have hq0 : q ≠ 0 := by
      intro hq
      subst q
      rcases hwhere with ⟨-, hq⟩ | ⟨-, hq⟩
      · omega
      · omega
    rw [hvq] at hmem
    exact hiso.2 q hq0 hqstart hmem

/-- **A component before the rotation point remains isolated after rotation.**

This is the missing mirror of `isIsolated_rotWord_of_le`.  The component moves
past the seam to index `|w|-i+a`.  Every non-seam component start of the rotated
word is sent back by `exists_isCompStart_of_rotWord_of_length_le`; the seam start
itself is handled by the component of `w` containing the rotation point. -/
theorem isIsolated_rotWord_before (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ x ∈ w, D.IsLetter x)
    (hclosed : RelLetter.listVal w = 1) {i a k : ℕ} (hi : i < w.length)
    (hcomp : IsComp lam w a k) (hki : k ≤ i) (ha0 : 0 < a)
    (hiso : IsIsolated D.fam lam v w a) :
    IsIsolated D.fam lam (vertex v w i) (rotWord w i)
      (w.length - i + a) := by
  have hak : a < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  have hai : a < i := by omega
  have hrotcomp : IsComp lam (rotWord w i)
      (w.length - i + a) (w.length - i + k) :=
    isComp_rotWord_before lam (le_of_lt hi) hcomp hki ha0
  have hdistVertex : vertex (vertex v w i) (rotWord w i)
      (w.length - i + a) = vertex v w a := by
    exact vertex_rotWord_add v w (le_of_lt hi) hclosed
      (w.length - i + a) a rfl (by omega)
  refine ⟨⟨w.length - i + k, hrotcomp⟩, ?_⟩
  intro p hpdist hpstart hconn
  have hmem : (vertex v w a)⁻¹ *
      vertex (vertex v w i) (rotWord w i) p ∈ D.fam lam := by
    rw [← hdistVertex]
    exact hconn
  rcases Nat.eq_zero_or_pos p with hp0 | hppos
  · subst hp0
    have hv0 : vertex (vertex v w i) (rotWord w i) 0 = vertex v w i := by
      rw [vertex_rotWord_le v w (le_of_lt hi) 0 (by omega), Nat.add_zero]
    obtain ⟨p₂, hp₂⟩ := hpstart
    have hiw : i < w.length := by omega
    have hci : (w[i]'hiw).IsCompOf lam := by
      have hc0 := hp₂.2.2.1 0 le_rfl hp₂.1 (by omega)
      rwa [getElem_rotWord_lt w (le_of_lt hi) 0 (i + 0) rfl (by omega) (by omega)
        (by omega)] at hc0
    obtain ⟨q, qk, hqi, hiqk, hqcomp⟩ :=
      exists_isComp_of_isCompOf lam w i hiw hci
    have hqa : q ≠ a := by
      intro hqa
      subst hqa
      have hends : qk = k := isComp_end_unique hqcomp hcomp
      omega
    have hqconn : Connected D.fam lam v w q i := by
      exact span_mem_fam D lam v hlet i (by omega) q hqi
        (fun m hm1 hm2 hm3 ⇒ hqcomp.2.2.1 m hm1 (by omega) hm3)
    rw [hv0] at hmem
    refine hiso.2 q hqa ⟨qk, hqcomp⟩ ?_
    have heq : (vertex v w a)⁻¹ * vertex v w q =
        ((vertex v w a)⁻¹ * vertex v w i) *
          ((vertex v w q)⁻¹ * vertex v w i)⁻¹ := by
      group
    rw [heq]
    exact mul_mem hmem (inv_mem hqconn)
  · obtain ⟨q, hqstart, hwhere, hvq⟩ :=
      exists_isCompStart_of_rotWord_of_length_le lam v hclosed (le_of_lt hi) hpstart
        (by omega)
    have hqa : q ≠ a := by
      intro hqa
      subst hqa
      rcases hwhere with ⟨-, hq⟩ | ⟨-, hq⟩
      · omega
      · omega
    rw [hvq] at hmem
    exact hiso.2 q hqa hqstart hmem

end OsinComponents
end GGT
end GroupApproximation
