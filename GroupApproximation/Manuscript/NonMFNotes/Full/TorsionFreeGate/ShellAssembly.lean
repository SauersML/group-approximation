import GroupApproximation.Manuscript.NonMFNotes.Full.TorsionFreeGate.LabelledMap

/-!
# From a shell to the Greendlinger witness (lane NN07a)

Word-level half of the classical `C'(1/6)` Greendlinger lemma
(`SmallCancellationRouter.GreendlingerGate`, `non_mf_group_notes.tex`, `thm:torsionfree`,
milestone 1 of L7; Lyndon–Schupp, Ch. V, Thm. 4.4).

In a reduced relator map with outer face through `o` reading `invRev w`:
* `six_mul_lt_of_interiorRun`: every arc glued to an interior neighbour is a piece, so under
  `C'(1/6)` it is shorter than a sixth of its face;
* `run_infix_of_outerRun`: an arc glued to the outer face spells a contiguous subword of `w`;
* `greendlingerWitness_of_shell`: a shell (one outer arc, at most three interior arcs) spells
  more than half of a symmetrized relator inside `w`, which is exactly the conclusion
  demanded by `SmallCancellationRouter.GreendlingerConclusion`.
-/

namespace GroupApproximation.Full.NN07a

open GroupApproximation.SmallCancellationRouter

universe u

namespace LabelledMap

variable {α : Type u} (M : LabelledMap α)

/-- An arc glued to an interior neighbouring face is a piece; under `C'(1/6)` it is short. -/
theorem six_mul_lt_of_interiorRun {R : Set (List (α × Bool))} {o y : M.Dart} {k : ℕ}
    (hsc : MetricSmallCancellation R (1 / 6))
    (hrel : ∀ d, ¬ M.OnFace o d → M.wordFrom d ∈ symmetrization R)
    (hred : M.IsReducedAway o) (hy : ¬ M.OnFace o y) (hrun : M.IsInteriorRun o y k)
    (hk : k ≤ M.flen y) : 6 * k < M.flen y := by
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · have := M.flen_pos y
    omega
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨hglue, hint⟩ := hrun
    have hopp : ¬ M.OnFace o (M.opp y) := hint hpos
    have hz : ¬ M.OnFace o (M.next (M.opp y)) := fun h => hopp (M.onFace_of_onFace_next h)
    have hw1 : M.wordFrom y ∈ symmetrization R := hrel y hy
    have hw2 : FreeGroup.invRev (M.wordFrom (M.next (M.opp y))) ∈ symmetrization R :=
      invRev_mem_symmetrization (hrel (M.next (M.opp y)) hz)
    have hne : M.wordFrom y ≠ FreeGroup.invRev (M.wordFrom (M.next (M.opp y))) :=
      hred y hy hopp
    have hpre1 : M.run y (k' + 1) <+: M.wordFrom y := by
      show M.run y (k' + 1) <+: M.run y (M.flen y)
      have e : M.flen y = (k' + 1) + (M.flen y - (k' + 1)) := by omega
      rw [e, M.run_add y (k' + 1) (M.flen y - (k' + 1))]
      exact List.prefix_append _ _
    have hpre2 : M.run y (k' + 1) <+: FreeGroup.invRev (M.wordFrom (M.next (M.opp y))) :=
      M.run_prefix_mirror hglue hk
    have hpiece : IsPiece (symmetrization R) (M.run y (k' + 1)) :=
      ⟨M.wordFrom y, hw1, FreeGroup.invRev (M.wordFrom (M.next (M.opp y))), hw2, hne,
        hpre1, hpre2⟩
    have hlt : ((M.run y (k' + 1)).length : ℚ) < 1 / 6 * ((M.wordFrom y).length : ℚ) :=
      hsc (M.run y (k' + 1)) hpiece (M.wordFrom y) hw1 hpre1
    rw [M.length_run, M.length_wordFrom] at hlt
    have h6 : ((6 * (k' + 1) : ℕ) : ℚ) < (M.flen y : ℚ) := by
      push_cast at hlt ⊢
      linarith
    exact_mod_cast h6

/-- An arc glued to the outer face spells a contiguous subword of the boundary word `w`. -/
theorem run_infix_of_outerRun {o x : M.Dart} {k : ℕ} {w : List (α × Bool)}
    (hout : M.wordFrom o = FreeGroup.invRev w) (h : M.IsOuterRun o x (k + 1)) :
    M.run x (k + 1) <:+: w := by
  obtain ⟨hglue, m, hm, hkm, hx⟩ := h
  have hg : M.next^[k] (M.opp (M.next^[k] x)) = M.opp x := hglue k (by omega)
  have e : m = k + (m - k) := by omega
  have hpos : M.opp (M.next^[k] x) = M.next^[m - k] o := by
    apply M.next_injective.iterate k
    rw [hg, hx, ← Function.iterate_add_apply, ← e]
  have hsub : M.run x (k + 1) = FreeGroup.invRev (M.run (M.next^[m - k] o) (k + 1)) := by
    rw [← hpos, ← M.invRev_run_of_glued x k hglue, FreeGroup.invRev_invRev]
  have hinf : M.run (M.next^[m - k] o) (k + 1) <:+: M.wordFrom o := by
    have e1 : M.flen o = (m - k) + (k + 1) + (M.flen o - (m + 1)) := by omega
    show M.run (M.next^[m - k] o) (k + 1) <:+: M.run o (M.flen o)
    rw [e1, M.run_add o ((m - k) + (k + 1)) (M.flen o - (m + 1)),
      M.run_add o (m - k) (k + 1)]
    exact List.infix_append _ _ _
  have h2 := invRev_infix hinf
  rw [← hsub, hout, FreeGroup.invRev_invRev] at h2
  exact h2

/-- **Shell to Greendlinger witness.**  A shell of a reduced `C'(1/6)` relator map whose outer
face reads `invRev w` yields the conclusion of `SmallCancellationRouter.GreendlingerConclusion`
for `w` (Lyndon–Schupp, Ch. V, proof of Thm. 4.4). -/
theorem greendlingerWitness_of_shell {R : Set (List (α × Bool))} {o x : M.Dart}
    {w : List (α × Bool)}
    (hsc : MetricSmallCancellation R (1 / 6))
    (hout : M.wordFrom o = FreeGroup.invRev w)
    (hrel : ∀ d, ¬ M.OnFace o d → M.wordFrom d ∈ symmetrization R)
    (hred : M.IsReducedAway o) (hx : M.IsShell o x) :
    ∃ r ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: r ∧ r.length < 2 * u.length := by
  obtain ⟨hxo, k, k₁, k₂, k₃, hsum, hk, hk₁, hk₂, hk₃⟩ := hx
  have hf1 : M.flen (M.next^[k] x) = M.flen x := M.flen_iterate x k
  have hf2 : M.flen (M.next^[k + k₁] x) = M.flen x := M.flen_iterate x (k + k₁)
  have hf3 : M.flen (M.next^[k + k₁ + k₂] x) = M.flen x := M.flen_iterate x (k + k₁ + k₂)
  have hy1 : ¬ M.OnFace o (M.next^[k] x) := fun h => hxo (M.onFace_of_onFace_iterate k h)
  have hy2 : ¬ M.OnFace o (M.next^[k + k₁] x) :=
    fun h => hxo (M.onFace_of_onFace_iterate (k + k₁) h)
  have hy3 : ¬ M.OnFace o (M.next^[k + k₁ + k₂] x) :=
    fun h => hxo (M.onFace_of_onFace_iterate (k + k₁ + k₂) h)
  have hl1 : k₁ ≤ M.flen (M.next^[k] x) := by
    rw [hf1]
    omega
  have hl2 : k₂ ≤ M.flen (M.next^[k + k₁] x) := by
    rw [hf2]
    omega
  have hl3 : k₃ ≤ M.flen (M.next^[k + k₁ + k₂] x) := by
    rw [hf3]
    omega
  have h1 : 6 * k₁ < M.flen (M.next^[k] x) :=
    M.six_mul_lt_of_interiorRun hsc hrel hred hy1 hk₁ hl1
  have h2 : 6 * k₂ < M.flen (M.next^[k + k₁] x) :=
    M.six_mul_lt_of_interiorRun hsc hrel hred hy2 hk₂ hl2
  have h3 : 6 * k₃ < M.flen (M.next^[k + k₁ + k₂] x) :=
    M.six_mul_lt_of_interiorRun hsc hrel hred hy3 hk₃ hl3
  rw [hf1] at h1
  rw [hf2] at h2
  rw [hf3] at h3
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine ⟨M.wordFrom x, hrel x hxo, M.run x (k' + 1), M.run_infix_of_outerRun hout hk, ?_, ?_⟩
  · show M.run x (k' + 1) <+: M.run x (M.flen x)
    have e : M.flen x = (k' + 1) + (k₁ + k₂ + k₃) := by omega
    rw [e, M.run_add x (k' + 1) (k₁ + k₂ + k₃)]
    exact List.prefix_append _ _
  · rw [M.length_wordFrom, M.length_run]
    omega

end LabelledMap

end GroupApproximation.Full.NN07a
