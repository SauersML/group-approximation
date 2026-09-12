import GroupApproximation.GGT.OsinTheorem54SepDistPrefix

/-!
# Components of the suffix past the first crossing

The other half of Lemma 5.10's inductive step.  The prefix before the first
penetration index separates nothing; here the suffix past the crossing is shown
to carry components of the whole word, which is what makes its separating count
strictly smaller.

## The general transfer, and the primitive behind its instances

`isComp_of_isComp_segment_general` supplies BOTH maximality clauses as
hypotheses.  The landed `isComp_of_isComp_segment` (interior), the prefix form
`isComp_of_isComp_segment'` (start free at `k = 0`) and the suffix form below
are its three instances, and the general form is where the shared clauses live.

The primitive that discharges the boundary clauses in every one of those
instances is `eq_of_isCompOf_of_isCompOf` --- **a letter carries one index**.
Three times now a boundary case has looked as though it needed a comparison of
component spans across a merge, and three times the merge turned out to be
impossible because the two indices involved are forced equal, or forced
distinct, by the letter itself.  When a boundary case here resists, that is the
first thing to reach for, not an estimate.

## Why the suffix is easier at the far end and harder at the near one

At the far end there is nothing to prove: the suffix runs to the end of `w`, so
either the component stops inside it and the segment's own clause applies, or it
reaches `|w|` and the clause is vacuous.

At the near end a component of the suffix starting at `a = 0` means `w[k₀]` is a
`μ`-letter, and the two sub-cases go by different mechanisms.  For `μ = λ` it is
impossible, by the crossing's own closing clause.  For `μ ≠ λ` it is possible
and simply goes through: `w[k₀-1]` lies inside the crossing so it is a
`λ`-letter, hence by the one-index fact not a `μ`-letter, so the `μ`-run does
not extend backwards and `k₀` is a genuine `μ`-component start of `w`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

omit [Group G] in
/-- **The component transfer, with both maximality clauses as hypotheses.**

The interior, prefix and suffix forms are its instances; see the module header
for the one-index primitive that discharges the hypotheses in each. -/
theorem isComp_of_isComp_segment_general (lam : Λ) (w : List (RelLetter G Λ))
    {k m a b : ℕ} (hcomp : IsComp lam ((w.drop k).take m) a b)
    (hstart : ∀ t : ℕ, k + a = t + 1 → ∀ ht : t < w.length,
      ¬ (w[t]'ht).IsCompOf lam)
    (hend : ∀ hn : k + b < w.length, ¬ (w[k + b]'hn).IsCompOf lam)
    (hkm : k + m ≤ w.length) :
    IsComp lam w (k + a) (k + b) := by
  obtain ⟨hab, hbl, hrange, -, -⟩ := hcomp
  have hseg : ((w.drop k).take m).length = min m (w.length - k) := by
    rw [List.length_take, List.length_drop]
  have hml : ((w.drop k).take m).length ≤ m := by
    rw [hseg]; omega
  refine ⟨by omega, by omega, ?_, hstart, hend⟩
  intro t ht1 ht2 ht
  have hts : t - k < ((w.drop k).take m).length := by omega
  rw [getElem_segment' w k m (t - k) t hts ht (by omega)]
  exact hrange (t - k) (by omega) (by omega) hts

omit [Group G] in
/-- **A component of the suffix past a crossing is a component of the word.**

The far end is free, the suffix running to the end of `w`.  At the near end,
`μ = λ` is impossible by the crossing's closing clause and `μ ≠ λ` goes through
by the one-index fact applied to `w[k₀-1]`. -/
theorem isComp_of_isComp_suffix (lam mu : Λ) (w : List (RelLetter G Λ))
    {n₀ k₀ a b : ℕ} (hcross : IsComp lam w n₀ k₀)
    (hcomp : IsComp mu ((w.drop k₀).take (w.length - k₀)) a b) :
    IsComp mu w (k₀ + a) (k₀ + b) := by
  obtain ⟨hn0k, hkw, hrangeL, -, hpostL⟩ := hcross
  have hlen : ((w.drop k₀).take (w.length - k₀)).length = w.length - k₀ :=
    length_segment w k₀ (w.length - k₀) (by omega)
  obtain ⟨hab, hbl, hrange, hpre, hpost⟩ := hcomp
  refine isComp_of_isComp_segment_general mu w ⟨hab, hbl, hrange, hpre, hpost⟩
    ?_ ?_ (by omega)
  · -- the near end
    intro t hteq ht hc
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · -- `a = 0`: the letter before the crossing's end is a `lam`-letter
      subst ha0
      have htk : t = k₀ - 1 := by omega
      subst htk
      have hk0pos : 0 < k₀ := by omega
      have hcl : (w[k₀ - 1]'ht).IsCompOf lam :=
        hrangeL (k₀ - 1) (by omega) (by omega) ht
      have hml : mu = lam := eq_of_isCompOf_of_isCompOf hc hcl
      -- but then `w[k₀]` would be a `lam`-letter, which the crossing forbids
      have hkw' : k₀ < w.length := by omega
      have hc0 : (w[k₀ + 0]'(by omega)).IsCompOf mu := by
        have h0 : (0 : ℕ) < ((w.drop k₀).take (w.length - k₀)).length := by omega
        have := hrange 0 le_rfl hab h0
        rwa [getElem_segment' w k₀ (w.length - k₀) 0 (k₀ + 0) h0 (by omega) rfl]
      rw [hml] at hc0
      exact hpostL hkw' (by simpa using hc0)
    · -- `a ≥ 1`: the segment's own clause
      have hts : a - 1 < ((w.drop k₀).take (w.length - k₀)).length := by omega
      rw [getElem_segment' w k₀ (w.length - k₀) (a - 1) t hts ht (by omega)] at hc
      exact hpre (a - 1) (by omega) hts hc
  · -- the far end
    intro hn hc
    have hblt : b < ((w.drop k₀).take (w.length - k₀)).length := by omega
    rw [getElem_segment' w k₀ (w.length - k₀) b (k₀ + b) hblt hn rfl] at hc
    exact hpost hblt hc

end OsinComponents
end GGT
end GroupApproximation
