import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchChord
import GroupApproximation.Meta.AxiomGuard

/-!
# Selecting the turn of an outer pinch

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  The section pinch step at an uncrossed turn
(`PocketFaceSet.exists_pinchStepSection_of_uncrossedTurn`) needs a turn `d₀ → e₀` of the boundary
cycle together with the first arrival `k₀` from `alpha d₀` at `e₀` and a dart `z₀` of the cycle at
the vertex outside the stretch from `alpha d₀` to `e₀`.  A pocket not in first-turn order has a turn
at which rotating from `e₀` meets an edge of the cycle before `alpha d₀`.  When no other passage
crosses that turn, such an edge gives `z₀`: either the dart met is on the cycle, or it is the
reversal of a cycle dart `d`, and the dart after `d` sits on the same side.

* `OuterPinchCorners.exists_firstArrival`: the first arrival along a rotation cycle.
* `OuterPinchCorners.false_of_between_of_pow`: a dart reached from `e` before `a` does not lie strictly
  between `a` and `e`.
* `OuterPinchCorners.exists_outside_of_not_firstTurn`: the dart `z₀` at an uncrossed non-first turn.
* `PocketFaceSet.exists_not_firstTurn`: a pocket not in first-turn order has a non-first turn.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides
open scoped Classical

namespace OuterPinchCorners

open OuterPinchIsolated

section Orbit

variable {α : Type*}

/-- **The first arrival** along a rotation cycle at a different point. -/
theorem exists_firstArrival [Finite α] {σ : Equiv.Perm α} {a e : α} (h : σ.SameCycle a e)
    (hne : a ≠ e) : ∃ k, 0 < k ∧ (σ ^ k) a = e ∧ ∀ t, 0 < t → t < k → (σ ^ t) a ≠ e := by
  have hex : ∃ k, 0 < k ∧ (σ ^ k) a = e := by
    obtain ⟨p, -, hp⟩ := exists_pow_lt_of_sameCycle h
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · rw [h0, pow_zero, Equiv.Perm.one_apply] at hp
      exact absurd hp hne
    · exact ⟨p, h0, hp⟩
  exact ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
    fun t ht htk hte => Nat.find_min hex htk ⟨ht, hte⟩⟩

/-- **Three points on a rotation cycle.**  With `e` first reached from `a` after `k₀` steps and `a`
first reached from `e` after `k` steps, the point `t` steps after `e`, with `0 < t < k`, is not
reached from `a` before `e`. -/
theorem false_of_between_of_pow [Finite α] {σ : Equiv.Perm α} {a e : α} {k₀ k t p : ℕ}
    (hne : a ≠ e) (hk₀ : (σ ^ k₀) a = e) (hk₀min : ∀ s, 0 < s → s < k₀ → (σ ^ s) a ≠ e)
    (hk : (σ ^ k) e = a) (hkmin : ∀ s, 0 < s → s < k → (σ ^ s) e ≠ a)
    (ht0 : 0 < t) (htk : t < k) (hpz : (σ ^ p) a = (σ ^ t) e)
    (hpe : ∀ b, 0 < b → b ≤ p → (σ ^ b) a ≠ e) : False := by
  obtain ⟨N, hN⟩ : ∃ N, Function.minimalPeriod σ a = N := ⟨_, rfl⟩
  have hpos : 0 < N := by
    rw [← hN]
    exact minimalPeriod_pos _ _
  have hper : (σ ^ N) a = a := by
    rw [← hN]
    exact pow_minimalPeriod_apply _ _
  have hinj : ∀ i j, i < N → j < N → (σ ^ i) a = (σ ^ j) a → i = j := fun i j hi hj h =>
    pow_eq_pow_below (by rw [hN]; exact hi) (by rw [hN]; exact hj) h
  have hk₀pos : 0 < k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h0 | h0
    · rw [h0, pow_zero, Equiv.Perm.one_apply] at hk₀
      exact absurd hk₀ hne
    · exact h0
  have hpk₀ : p < k₀ := by
    by_contra hge
    push Not at hge
    exact hpe k₀ hk₀pos hge hk₀
  have hk₀N : k₀ < N := by
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hlt | heq
    · refine hk₀min (k₀ - N) (Nat.sub_pos_of_lt hlt) (by omega) ?_
      have h1 := hk₀
      rwa [← Nat.sub_add_cancel hlt.le, pow_add_apply, hper] at h1
    · rw [← heq, hper] at hk₀
      exact hne hk₀
  -- The two first arrivals add up to the minimal period.
  have hsum : (σ ^ (k + k₀)) a = a := by
    rw [pow_add_apply, hk₀, hk]
  have hNle : N ≤ k + k₀ := by
    rw [← hN]
    refine Function.IsPeriodicPt.minimalPeriod_le (by omega) ?_
    change (⇑σ)^[k + k₀] a = a
    rw [Equiv.Perm.iterate_eq_pow]
    exact hsum
  have hNeq : N = k + k₀ := by
    by_contra hne'
    refine hkmin (N - k₀) (Nat.sub_pos_of_lt hk₀N) (by omega) ?_
    rw [← hk₀, ← pow_add_apply, Nat.sub_add_cancel hk₀N.le, hper]
  have hz : (σ ^ (t + k₀)) a = (σ ^ t) e := by
    rw [pow_add_apply, hk₀]
  have := hinj p (t + k₀) (by omega) (by omega) (hpz.trans hz.symm)
  omega

end Orbit

section Walk

variable {M : CombMap.{u}} {c : List M.Dart}

/-- **The dart outside the stretch at an uncrossed non-first turn.**  For a list in walk order, a
turn `d₀ → e₀` that no other passage crosses and that is not a first turn has a dart `z₀` of the list
at the vertex, other than `e₀`, outside the stretch from `alpha d₀` to `e₀`. -/
theorem exists_outside_of_not_firstTurn (hne : c ≠ []) (hnodup : c.Nodup)
    (hc : ∀ d ∈ c, M.alpha d ∉ c)
    (hchain : c.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hcloses : M.vertexOf (M.alpha (c.getLast hne)) = M.vertexOf (c.head hne))
    {d₀ e₀ : M.Dart} (hd₀ : d₀ ∈ c) (hnext₀ : c.next d₀ hd₀ = e₀)
    (huncross : ∀ d (hd : d ∈ c), d ≠ d₀ → M.sigma.SameCycle (M.alpha d₀) (M.alpha d) →
      (RotationBetween M (M.alpha d₀) e₀ (M.alpha d) ↔ RotationBetween M (M.alpha d₀) e₀ (c.next d hd)))
    {k₀ : ℕ} (hk₀ : (M.sigma ^ k₀) (M.alpha d₀) = e₀)
    (hk₀min : ∀ t, 0 < t → t < k₀ → (M.sigma ^ t) (M.alpha d₀) ≠ e₀)
    (hnot : ¬ FirstTurn M (c.reverse.map M.alpha) (M.alpha e₀) (M.alpha d₀)) :
    ∃ z₀ ∈ c, M.sigma.SameCycle (M.alpha d₀) z₀ ∧ z₀ ≠ e₀ ∧ ¬ RotationBetween M (M.alpha d₀) e₀ z₀ := by
  have he₀ : e₀ ∈ c := by
    rw [← hnext₀]
    exact List.next_mem ..
  have hαe : M.alpha d₀ ≠ e₀ := fun h => hc d₀ hd₀ (by rw [h]; exact he₀)
  have hvert : M.vertexOf (M.alpha d₀) = M.vertexOf e₀ := by
    have h := rel_next_of_isChain hne hnodup hchain hcloses hd₀
    rwa [hnext₀] at h
  have hsame : M.sigma.SameCycle (M.alpha d₀) e₀ := (M.vertexOf_eq_iff _ _).mp hvert
  obtain ⟨k, hk0, hk, hkmin⟩ := exists_firstArrival hsame.symm hαe.symm
  have hex : ∃ t, 0 < t ∧ t < k ∧ walkKeep M c ((M.sigma ^ t) e₀) := by
    by_contra hno
    push Not at hno
    exact hnot (FirstTurn.reverse_map_alpha_iff.mpr ⟨k, hk0, hk, hno⟩)
  obtain ⟨t, ht0, htk, hkeep⟩ := hex
  have hout : ¬ RotationBetween M (M.alpha d₀) e₀ ((M.sigma ^ t) e₀) := by
    rintro ⟨p, -, hpz, hpe⟩
    exact false_of_between_of_pow hαe hk₀ hk₀min hk hkmin ht0 htk hpz hpe
  have hzv : M.sigma.SameCycle (M.alpha d₀) ((M.sigma ^ t) e₀) :=
    hsame.trans (sameCycle_of_pow_eq rfl)
  have hza : (M.sigma ^ t) e₀ ≠ M.alpha d₀ := hkmin t ht0 htk
  have hprev : ∀ (a b : M.Dart) (ha : a ∈ c) (hb : b ∈ c), a = b → c.prev a ha = c.prev b hb := by
    rintro a b ha hb rfl
    rfl
  rcases hkeep with hz | hz
  · refine ⟨_, hz, hzv, fun h => hkmin (k - t) (by omega) (by omega) ?_, hout⟩
    rw [← h, ← pow_add_apply, Nat.sub_add_cancel htk.le]
    exact hk
  · have hdne : M.alpha ((M.sigma ^ t) e₀) ≠ d₀ := fun h => hza (by rw [← h, M.alpha_involutive])
    have hv' : M.sigma.SameCycle (M.alpha d₀) (M.alpha (M.alpha ((M.sigma ^ t) e₀))) := by
      rw [M.alpha_involutive]
      exact hzv
    have hv2 := rel_next_of_isChain hne hnodup hchain hcloses hz
    rw [M.alpha_involutive] at hv2
    refine ⟨c.next _ hz, List.next_mem .., hzv.trans ((M.vertexOf_eq_iff _ _).mp hv2),
      fun h => hdne (((List.prev_next c hnodup _ hz).symm.trans
        (hprev _ _ _ _ (h.trans hnext₀.symm))).trans (List.prev_next c hnodup d₀ hd₀)), fun h => ?_⟩
    have h' := (huncross _ hz hdne hv').mpr h
    rw [M.alpha_involutive] at h'
    exact hout h'

end Walk

end OuterPinchCorners

open OuterPinchIsolated OuterPinchCorners

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A pocket not in first-turn order has a non-first turn.** -/
theorem exists_not_firstTurn (K : PocketFaceSet D eps X lo hi) (h : ¬ K.FirstTurns) :
    ∃ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle),
      ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
        (X.toCombMap.alpha (K.boundary.cycle.next d₀ hd₀)) (X.toCombMap.alpha d₀) := by
  by_contra hno
  push Not at hno
  exact h (isChain_of_rel_next K.boundary.cycle_nonempty K.boundary.cycle_nodup
    (R := fun d e => FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha e) (X.toCombMap.alpha d)) hno)

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCorners.exists_firstArrival
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCorners.false_of_between_of_pow
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCorners.exists_outside_of_not_firstTurn
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.exists_not_firstTurn
