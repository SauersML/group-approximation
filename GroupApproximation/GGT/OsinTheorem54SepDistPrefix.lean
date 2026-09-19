import GroupApproximation.GGT.OsinTheorem54SepDistBase
import GroupApproximation.GGT.OsinTheorem54SepEnum
import GroupApproximation.GGT.OsinTheorem54SepTransport

/-!
# The prefix before the first separating coset separates nothing

The inductive step of Lemma 5.10's left half cuts a geodesic at the FIRST
penetration index, globally over all `λ`, and this module supplies the half that
says the piece before the cut is a single letter of `Y`.

## Why the cut has to be global

Cutting at the first `λ`-index for one `λ` does not work: the boundary case
where a `μ`-run of the prefix reaches the cut is then unresolved for `μ ≠ λ`,
and closing it looks as though it needs a comparison of spans across a merge.
Cutting at the global minimum removes that, by an observation about letters
rather than about geometry:

* `eq_of_isCompOf_of_isCompOf` --- **a letter carries one index.**  `IsCompOf`
  is `base _ => False | comp ν _ => ν = λ`, so a letter that is a `λ`-letter and
  a `μ`-letter has `λ = μ`.  Two components of different indices therefore never
  start at the same position.

With that, a `μ`-run of the prefix reaching the cut at `n₀` splits into two
cases and neither survives.  If `w[n₀]` is not a `μ`-letter the run is a maximal
`μ`-run of `w` starting below `n₀`, with *literally the same span*, so it is an
essential penetration below the global minimum.  And if `w[n₀]` IS a `μ`-letter
then `μ = λ`, because `n₀` starts a `λ`-component --- so `w[n₀-1]` is a
`λ`-letter, contradicting the closing clause that makes `n₀` a component start.
No spans are compared.

`isComp_of_isComp_segment'` generalises the landed transfer to both boundary
positions: the start is free when the segment begins where the word does, and
the end is supplied as a hypothesis rather than derived.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

omit [Group G] in
/-- **A letter carries one index.** -/
theorem eq_of_isCompOf_of_isCompOf {a : RelLetter G Λ} {lam mu : Λ}
    (hl : a.IsCompOf lam) (hm : a.IsCompOf mu) : lam = mu := by
  cases a with
  | base x => exact absurd hl not_false
  | comp nu h => exact hl.symm.trans hm

omit [Group G] in
/-- **The component transfer, at both boundary positions.**  The start is free
when the segment begins where the word does; the end is a hypothesis. -/
theorem isComp_of_isComp_segment' (lam : Λ) (w : List (RelLetter G Λ))
    {k m a b : ℕ} (hcomp : IsComp lam ((w.drop k).take m) a b)
    (hstart : 1 ≤ a ∨ k = 0)
    (hend : ∀ hn : k + b < w.length, ¬ (w[k + b]'hn).IsCompOf lam)
    (hkm : k + m ≤ w.length) :
    IsComp lam w (k + a) (k + b) := by
  obtain ⟨hab, hbl, hrange, hpre, -⟩ := hcomp
  have hseg : ((w.drop k).take m).length = min m (w.length - k) := by
    rw [List.length_take, List.length_drop]
  have hml : ((w.drop k).take m).length ≤ m := by
    rw [hseg]; omega
  refine ⟨by omega, by omega, ?_, ?_, hend⟩
  · intro t ht1 ht2 ht
    have hts : t - k < ((w.drop k).take m).length := by omega
    rw [getElem_segment' w k m (t - k) t hts ht (by omega)]
    exact hrange (t - k) (by omega) (by omega) hts
  · intro t hteq ht hc
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · -- `a = 0`: then `hstart` forces `k = 0`, and `0 = t + 1` is impossible
      subst ha0
      rcases hstart with ha | hk0
      · omega
      · omega
    · -- `a ≥ 1`: the segment's own opening clause
      have hts : a - 1 < ((w.drop k).take m).length := by omega
      rw [getElem_segment' w k m (a - 1) t hts ht (by omega)] at hc
      exact hpre (a - 1) (by omega) hts hc

/-- **A least penetration index exists**, once there is one at all. -/
theorem exists_min_penetration (P : ℕ → Prop) (h : ∃ m, P m) :
    ∃ n₀, P n₀ ∧ ∀ m, m < n₀ → ¬ P m := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun m hm => Nat.find_min h hm⟩

/-- **The prefix before the first separating coset separates nothing.**

`n₀` is the least penetration index over ALL indices; `hmin` says so.  The
conclusion holds for every `μ`, which is what `Y`'s definition needs. -/
theorem sepSet_prefix_eq_empty (D : RelGenSet G Λ) (Dc : ℕ)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc) {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w)
    {lam : Λ} {n₀ k₀ : ℕ} (hcomp : IsComp lam w n₀ k₀)
    (hmin : ∀ (mu : Λ) (m : ℕ) (c : G ⧸ D.fam mu), m < n₀ →
      c ∈ sepSet D mu Dc f g → ¬ PenetratesAt D mu Dc f w m c)
    (mu : Λ) :
    sepSet D mu Dc f (vertex f w n₀) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro c'' hc''
  obtain ⟨hn0k, hkw, hrangeL, hpreL, -⟩ := hcomp
  have hn0le : n₀ ≤ w.length := by omega
  have hseg := isGeodesicWord_segment D hw (Nat.zero_le n₀) hn0le
  rw [vertex_zero] at hseg
  obtain ⟨a, b, hEP, hcc⟩ := (h48 mu).1 f (vertex f w n₀)
    ((w.drop 0).take (n₀ - 0)) hseg c'' hc''
  have hlen : ((w.drop 0).take (n₀ - 0)).length = n₀ - 0 :=
    length_segment w 0 (n₀ - 0) (by omega)
  obtain ⟨hab, hbl, hrange, hpre, hpost⟩ := hEP
  -- the closing clause of the transfer, in both boundary positions
  have hend : ∀ hn : 0 + b < w.length, ¬ (w[0 + b]'hn).IsCompOf mu := by
    intro hn hc
    rw [getElem_congr_idx (Nat.zero_add b)] at hc
    have hbw : b < w.length := by omega
    -- pin the proof argument, so later steps do not carry two proofs of one bound
    have hc' : (w[b]'hbw).IsCompOf mu := hc
    by_cases hblt : b < ((w.drop 0).take (n₀ - 0)).length
    · rw [getElem_segment' w 0 (n₀ - 0) b b hblt hbw (by omega)] at hc'
      exact hpost hblt hc'
    · -- the run reaches the cut: `w[n₀]` is a `μ`-letter, so `μ = lam`
      have hbn : b = n₀ := by omega
      have hcl : (w[b]'hbw).IsCompOf lam :=
        hrangeL b (by omega) (by omega) hbw
      have hml : mu = lam := eq_of_isCompOf_of_isCompOf hc' hcl
      -- then the letter before the cut is a `lam`-letter, which `n₀` forbids
      have hb1 : b - 1 < ((w.drop 0).take (n₀ - 0)).length := by omega
      have hb1w : b - 1 < w.length := by omega
      have hprev := hrange (b - 1) (by omega) (by omega) hb1
      rw [← getElem_segment' w 0 (n₀ - 0) (b - 1) (b - 1) hb1 hb1w (by omega)]
        at hprev
      rw [hml] at hprev
      exact hpreL (b - 1) (by omega) hb1w hprev
  -- transfer the component and its span, then contradict minimality
  have hcompw : IsComp mu w (0 + a) (0 + b) :=
    isComp_of_isComp_segment' mu w ⟨hab, hbl, hrange, hpre, hpost⟩
      (Or.inr rfl) hend (by omega)
  have hccw : c'' = QuotientGroup.mk (vertex f w (0 + a)) := by
    have hv := vertex_segment w f 0 (n₀ - 0) a (by omega)
    rw [vertex_zero] at hv
    rw [hcc, hv]
  -- the membership comes from Definition 4.3's own witness, spliced into `w`,
  -- not from asking 4.8 for an essential penetration it does not give
  have hc''0 : c'' ∈ sepSet D mu Dc (vertex f w 0) (vertex f w n₀) := by
    rw [vertex_zero]
    exact hc''
  have hmem : c'' ∈ sepSet D mu Dc f g :=
    sepSet_of_sepSet_segment D mu Dc hw (Nat.zero_le n₀) hn0le hc''0
  exact hmin mu (0 + a) c'' (by omega) hmem ⟨⟨0 + b, hcompw⟩, hccw⟩

end OsinComponents
end GGT
end GroupApproximation
