import GroupApproximation.GGT.DGOShortCycleIndices

/-!
# Two connectors, by composing the splice with itself

Dahmani--Guirardel--Osin's Case 4b2 builds a cycle with *two* connectors.  It is
not a new construction: splicing the far pair first leaves the near pair intact,
so the second splice is `cycle_of_connector` again.  What blocks the composition
as stated is only that `cycle_of_connector` concludes with an existential and so
forgets that its witness IS `w.take m ++ (r ++ w.drop j)` --- and the second
splice needs that, to know its own indices survive.  `cycle_of_connector_splice`
is the same theorem with the witness exposed, and `cycle_of_two_connectors` is
the composition.

## Why the far pair goes first, and what is still open

A splice deletes the indices strictly between its two.  Splicing the near pair
`(m, j₁)` first would delete `m₂` when `m₂ < j₂` sits inside it; splicing the far
pair `(m₂, j₂)` first keeps every index below `m₂`, and `m ≤ j₁ ≤ m₂` puts both
of the near indices there.  So the hypothesis `j₁ ≤ m₂` is what makes the
composition legal, and it is exactly the condition that the two pairs do not
interleave.

The interleaved configuration is genuinely outside this lemma: with overlapping
intervals there is no middle segment to keep, and the cycle
Dahmani--Guirardel--Osin write for it traverses part of a side *backwards*
(their `[v,z]`, read from whichever of the two near-vertices comes second).
That needs `revWord` of a segment and is the one place their reflection symmetry
cannot be dodged by instantiating twice.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The splice, with its witness exposed.**  Identical in content to
`cycle_of_connector`; the conclusion names the word instead of quantifying over
it, which is what lets a second splice compute with its vertices. -/
theorem cycle_of_connector_splice (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hcl : RelLetter.listVal w = 1)
    (hcomp : IsComp lam w 0 1) (hiso : IsIsolated D.fam lam v w 0)
    {m j : ℕ} (hmj : m ≤ j) (hjw : j ≤ w.length)
    {r : List (RelLetter G Λ)} (hrlet : ∀ a ∈ r, D.IsLetter a)
    (hrval : RelLetter.listVal r = (vertex v w m)⁻¹ * vertex v w j)
    (hrcos : ∀ p : ℕ, p ≤ r.length →
      v⁻¹ * vertex (vertex v w m) r p ∉ D.fam lam) :
    (∀ a ∈ w.take m ++ (r ++ w.drop j), D.IsLetter a) ∧
      RelLetter.listVal (w.take m ++ (r ++ w.drop j)) = 1 ∧
      (w.take m ++ (r ++ w.drop j)).length = m + r.length + (w.length - j) ∧
      IsComp lam (w.take m ++ (r ++ w.drop j)) 0 1 ∧
      IsIsolated D.fam lam v (w.take m ++ (r ++ w.drop j)) 0 ∧
      (vertex v (w.take m ++ (r ++ w.drop j)) 0)⁻¹ *
          vertex v (w.take m ++ (r ++ w.drop j)) 1
        = (vertex v w 0)⁻¹ * vertex v w 1 := by
  have hmw : m ≤ w.length := le_trans hmj hjw
  have h1w : 1 ≤ w.length := hcomp.2.1
  have hm0 : m ≠ 0 := by
    intro h
    refine hrcos 0 (Nat.zero_le _) ?_
    subst h
    simp only [vertex_zero, inv_mul_cancel]
    exact one_mem _
  have hm1 : m ≠ 1 := by
    intro h
    refine hrcos 0 (Nat.zero_le _) ?_
    subst h
    have hspan := span_mem_fam_of_isComp D v hlet hcomp
    rw [vertex_zero] at hspan
    simpa only [vertex_zero] using hspan
  have hm2 : 2 ≤ m := by omega
  obtain ⟨hv1, hv2, hv3⟩ := vertex_splice v w r hmw hrval
  have hqlen : (w.take m ++ (r ++ w.drop j)).length
      = m + r.length + (w.length - j) := by
    rw [List.length_append, List.length_append, List.length_take,
      List.length_drop]
    omega
  have hw0 : (w[0]'(by omega)).IsCompOf lam :=
    hcomp.2.2.1 0 le_rfl (by omega) (by omega)
  have hw1 : ∀ h1 : 1 < w.length, ¬ (w[1]'h1).IsCompOf lam := hcomp.2.2.2.2
  have hqcomp : IsComp lam (w.take m ++ (r ++ w.drop j)) 0 1 := by
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · intro i _ hi1 hiq
      have hi0 : i = 0 := by omega
      subst hi0
      rw [getElem_splice_left (i := 0) w r hmw (by omega) hiq]
      exact hw0
    · intro i hcon
      exact absurd hcon (by omega)
    · intro hk hcon
      rw [getElem_splice_left (i := 1) w r hmw (by omega) hk] at hcon
      exact hw1 (by omega) hcon
  have hAB : RelLetter.listVal (w.take j) * RelLetter.listVal (w.drop j) = 1 := by
    rw [← listVal_append, List.take_append_drop]
    exact hcl
  have htj : RelLetter.listVal (w.take j) = v⁻¹ * vertex v w j := by
    rw [vertex_eq_mul_listVal_take, inv_mul_cancel_left]
  have htm : RelLetter.listVal (w.take m) = v⁻¹ * vertex v w m := by
    rw [vertex_eq_mul_listVal_take, inv_mul_cancel_left]
  have hdj : RelLetter.listVal (w.drop j) = (vertex v w j)⁻¹ * v := by
    rw [htj] at hAB
    calc RelLetter.listVal (w.drop j)
        = (v⁻¹ * vertex v w j)⁻¹ *
            ((v⁻¹ * vertex v w j) * RelLetter.listVal (w.drop j)) := by group
      _ = (v⁻¹ * vertex v w j)⁻¹ := by rw [hAB, mul_one]
      _ = (vertex v w j)⁻¹ * v := by group
  refine ⟨?_, ?_, hqlen, hqcomp, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hlet a (List.take_subset m w h)
    · rcases List.mem_append.mp h with h' | h'
      · exact hrlet a h'
      · exact hlet a (List.drop_subset j w h')
  · rw [listVal_append, listVal_append, htm, hrval, hdj]
    group
  · refine isIsolated_zero_of_notMem D lam v hqcomp ?_
    intro i hine hiq hci
    rcases Nat.lt_or_ge i m with hlt | hge
    · rw [getElem_splice_left (i := i) w r hmw hlt hiq] at hci
      rw [hv1 i (le_of_lt hlt)]
      exact notMem_coset_of_isIsolated_zero D lam v hlet hcomp hiso (p := i)
        (by omega) hci (Nat.pos_of_ne_zero hine)
    · rcases Nat.lt_or_ge i (m + r.length) with hlt2 | hge2
      · have hidx : m + (i - m) = i := by omega
        have hveq : vertex v (w.take m ++ (r ++ w.drop j)) i
            = vertex (vertex v w m) r (i - m) := by
          have h := hv2 (i - m) (by omega)
          rwa [hidx] at h
        rw [hveq]
        exact hrcos (i - m) (by omega)
      · have hidx : m + r.length + (i - m - r.length) = i := by omega
        have hveq : vertex v (w.take m ++ (r ++ w.drop j)) i
            = vertex v w (j + (i - m - r.length)) := by
          have h := hv3 (i - m - r.length)
          rwa [hidx] at h
        rw [getElem_splice_right (i := i) w r hge2 hmw hiq] at hci
        rw [hveq]
        exact notMem_coset_of_isIsolated_zero D lam v hlet hcomp hiso
          (p := j + (i - m - r.length)) (by omega) hci (by omega)
  · rw [hv1 0 (by omega), hv1 1 (by omega)]
/-- **Two connectors, by composing the splice with itself.**  The far pair is
spliced first, which keeps every index below `m₂`, so the near pair `m ≤ j₁ ≤ m₂`
survives and the second splice is legal. -/
theorem cycle_of_two_connectors (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a)
    (hcl : RelLetter.listVal w = 1)
    (hcomp : IsComp lam w 0 1) (hiso : IsIsolated D.fam lam v w 0)
    {m j₁ m₂ j₂ : ℕ} (h1 : m ≤ j₁) (h2 : j₁ ≤ m₂) (h3 : m₂ ≤ j₂)
    (h4 : j₂ ≤ w.length)
    {r r' : List (RelLetter G Λ)}
    (hrlet : ∀ a ∈ r, D.IsLetter a)
    (hrval : RelLetter.listVal r = (vertex v w m)⁻¹ * vertex v w j₁)
    (hrcos : ∀ p : ℕ, p ≤ r.length →
      v⁻¹ * vertex (vertex v w m) r p ∉ D.fam lam)
    (hr'let : ∀ a ∈ r', D.IsLetter a)
    (hr'val : RelLetter.listVal r' = (vertex v w m₂)⁻¹ * vertex v w j₂)
    (hr'cos : ∀ p : ℕ, p ≤ r'.length →
      v⁻¹ * vertex (vertex v w m₂) r' p ∉ D.fam lam) :
    ∃ q : List (RelLetter G Λ),
      (∀ a ∈ q, D.IsLetter a) ∧ RelLetter.listVal q = 1 ∧
      q.length = m + r.length + ((m₂ - j₁) + r'.length + (w.length - j₂)) ∧
      IsComp lam q 0 1 ∧ IsIsolated D.fam lam v q 0 ∧
      (vertex v q 0)⁻¹ * vertex v q 1 = (vertex v w 0)⁻¹ * vertex v w 1 := by
  obtain ⟨hl1, hc1, hlen1, hcomp1, hiso1, hspan1⟩ :=
    cycle_of_connector_splice D lam v hlet hcl hcomp hiso h3 h4 hr'let hr'val
      hr'cos
  obtain ⟨hu1, -, -⟩ := vertex_splice v w r' (le_trans h3 h4) hr'val
  have hvm : vertex v (w.take m₂ ++ (r' ++ w.drop j₂)) m = vertex v w m :=
    hu1 m (by omega)
  have hvj : vertex v (w.take m₂ ++ (r' ++ w.drop j₂)) j₁ = vertex v w j₁ :=
    hu1 j₁ (by omega)
  have hrval2 : RelLetter.listVal r
      = (vertex v (w.take m₂ ++ (r' ++ w.drop j₂)) m)⁻¹ *
        vertex v (w.take m₂ ++ (r' ++ w.drop j₂)) j₁ := by
    rw [hvm, hvj]
    exact hrval
  have hrcos2 : ∀ p : ℕ, p ≤ r.length →
      v⁻¹ * vertex (vertex v (w.take m₂ ++ (r' ++ w.drop j₂)) m) r p
        ∉ D.fam lam := by
    rw [hvm]
    exact hrcos
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ :=
    cycle_of_connector D lam v hl1 hc1 hcomp1 hiso1 h1 (by omega) hrlet
      hrval2 hrcos2
  refine ⟨q, hq1, hq2, ?_, hq4, hq5, ?_⟩
  · rw [hq3, hlen1]
    omega
  · rw [hq6, hspan1]

end OsinComponents
end GGT
end GroupApproximation
