import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchIsolated
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEulerNoninterleaving
import GroupApproximation.Meta.AxiomGuard

/-!
# The split at an uncrossed turn of an outer pinch

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  A pocket face set in walk order that is not in first-turn order has a turn
`d₀ → e₀` for which rotating from `e₀` first meets another edge of the cycle before `alpha d₀`.  An
isolated turn (`Estimating/OsinPocketOuterPinchIsolated.lean`) need not exist: at a vertex with the
rotation `o₁ i₁ o₂ i₂ o₃ i₃ o₄ i₄` (`i = alpha d`, `o = e`) and the turns `i₁ → o₁`, `i₃ → o₃`,
`i₂ → o₄`, `i₄ → o₂`, no passage crosses another, the order is not first-turn order, and no turn is
isolated.  This module splits at any turn that no other passage at its vertex crosses
(`RotationBetween` on both ends, as in `PassagesNoninterleaving`).

The split darts are `x`, reached from `e₀` past darts off the edges of the cycle, and `y`, which
reaches `alpha d₀` past such darts.  Measured along the rotation cycle of `alpha d₀` below its minimal
period `N`, the dart `e₀` sits at position `k₀`, `x` at `m + k₀` and `y` at `N - q`.  The passages
strictly between `alpha d₀` and `e₀` sit below `k₀`, and every other passage sits after `x` and no
later than `y`.  So a turn is kept in one of three ways (`PinchSplit.Input.ChordKept`): its stretch
avoids the split darts, or both ends run into `y` without passing `x`, or both ends run into `x`
without passing `y`.

* `OuterPinchChord.runsIntoX_of_pos`, `runsIntoY_of_pos`: stretches measured by positions.
* `OuterPinchChord.chord_positions`: the positions above.
* `OuterPinchChord.chordKept_of_uncrossed`: every turn is kept, for a list in walk order.
* `PocketFaceSet.exists_pinchStepSection_of_uncrossedTurn`: the conclusion of the section pinch step
  at an uncrossed turn, with both proper arcs.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides
open scoped Classical

namespace PinchSplit.Input

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} (I : Input Delta)

/-- **A turn kept at a split at an uncrossed turn**: a kept turn (`TurnKept`), or both `a` and `b`
run into `x` without passing `y`. -/
def ChordKept (a b : Delta.toCombMap.Dart) : Prop :=
  I.TurnKept a b ∨
    ((∃ n : ℕ, (Delta.toCombMap.sigma ^ n) a = I.x ∧
        ∀ i ≤ n, (Delta.toCombMap.sigma ^ i) a ≠ I.y) ∧
      ∃ n : ℕ, (Delta.toCombMap.sigma ^ n) b = I.x ∧
        ∀ i ≤ n, (Delta.toCombMap.sigma ^ i) b ≠ I.y)

/-- **A kept turn stays on one new vertex.** -/
theorem vertexOf_eq_of_chordKept {a b : Delta.toCombMap.Dart} (h : I.ChordKept a b) :
    I.diagram.toCombMap.vertexOf a = I.diagram.toCombMap.vertexOf b := by
  rcases h with h | ⟨⟨n₁, hn₁, hy₁⟩, n₂, hn₂, hy₂⟩
  · exact I.vertexOf_eq_of_turnKept h
  · exact ((I.diagram.toCombMap.vertexOf_eq_iff a I.x).mpr (I.sameCycle_x_of_stretch hn₁ hy₁)).trans
      ((I.diagram.toCombMap.vertexOf_eq_iff b I.x).mpr (I.sameCycle_x_of_stretch hn₂ hy₂)).symm

end PinchSplit.Input

namespace OuterPinchChord

open OuterPinchIsolated

section Orbit

variable {α : Type*} {σ : Equiv.Perm α} {a x y : α} {N m k q : ℕ}

/-- **A position no later than `x` runs into `x` without passing `y`.** -/
theorem runsIntoX_of_pos
    (hinj : ∀ i j, i < N → j < N → (σ ^ i) a = (σ ^ j) a → i = j)
    (hq0 : 0 < q) (hmk : m + k < N - q) (hxpos : (σ ^ (m + k)) a = x)
    (hypos : (σ ^ (N - q)) a = y) {p : ℕ} (hp : p ≤ m + k) {z : α} (hz : (σ ^ p) a = z) :
    ∃ n : ℕ, (σ ^ n) z = x ∧ ∀ i ≤ n, (σ ^ i) z ≠ y := by
  refine ⟨m + k - p, ?_, fun i hi hy' => ?_⟩
  · rw [← hz, ← pow_add_apply, Nat.sub_add_cancel hp, hxpos]
  · have h1 : (σ ^ (i + p)) a = y := by
      rw [pow_add_apply, hz]
      exact hy'
    have := hinj (i + p) (N - q) (by omega) (by omega) (h1.trans hypos.symm)
    omega

/-- **A position after `x` and no later than `y` runs into `y` without passing `x`.** -/
theorem runsIntoY_of_pos
    (hinj : ∀ i j, i < N → j < N → (σ ^ i) a = (σ ^ j) a → i = j)
    (hq0 : 0 < q) (hxpos : (σ ^ (m + k)) a = x) (hypos : (σ ^ (N - q)) a = y)
    {p : ℕ} (hp : m + k < p) (hpN : p ≤ N - q) {z : α} (hz : (σ ^ p) a = z) :
    ∃ n : ℕ, (σ ^ n) z = y ∧ ∀ i ≤ n, (σ ^ i) z ≠ x := by
  refine ⟨N - q - p, ?_, fun i hi hx => ?_⟩
  · rw [← hz, ← pow_add_apply, Nat.sub_add_cancel hpN, hypos]
  · have h1 : (σ ^ (i + p)) a = x := by
      rw [pow_add_apply, hz]
      exact hx
    have := hinj (i + p) (m + k) (by omega) (by omega) (h1.trans hxpos.symm)
    omega

end Orbit

section Walk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {c : List X.toCombMap.Dart}

/-- **Positions at an uncrossed turn.**  Along the rotation cycle of `alpha d₀`, below its minimal
period `N`: `e₀` first at `k₀`, `x` at `m + k₀`, `y` at `N - q`, with `m + k₀ < N - q`.  The darts
strictly between `alpha d₀` and `e₀` sit below `k₀`, and every other dart on an edge of the cycle at
the vertex sits after `x` and no later than `y`. -/
theorem chord_positions (I : PinchSplit.Input X) (hc : ∀ d ∈ c, X.toCombMap.alpha d ∉ c)
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ c) (he₀ : e₀ ∈ c)
    {k₀ m q : ℕ} (hk₀ : (X.toCombMap.sigma ^ k₀) (X.toCombMap.alpha d₀) = e₀)
    (hk₀min : ∀ t, 0 < t → t < k₀ → (X.toCombMap.sigma ^ t) (X.toCombMap.alpha d₀) ≠ e₀)
    (hm : (X.toCombMap.sigma ^ m) e₀ = I.x)
    (hkeepm : ∀ t, 0 < t → t ≤ m → ¬ walkKeep X.toCombMap c ((X.toCombMap.sigma ^ t) e₀))
    (hq : (X.toCombMap.sigma ^ q) I.y = X.toCombMap.alpha d₀)
    (hkeepq : ∀ t, 0 < t → t < q → ¬ walkKeep X.toCombMap c ((X.toCombMap.sigma ^ t) I.y))
    {z₀ : X.toCombMap.Dart} (hz₀ : walkKeep X.toCombMap c z₀)
    (hz₀v : X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) z₀)
    (hz₀a : z₀ ≠ X.toCombMap.alpha d₀) (hz₀e : z₀ ≠ e₀)
    (hz₀out : ¬ RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ z₀) :
    ∃ N : ℕ, 0 < N ∧ k₀ < N ∧ q ≤ N ∧ m + k₀ < N - q ∧
      (X.toCombMap.sigma ^ (m + k₀)) (X.toCombMap.alpha d₀) = I.x ∧
      (X.toCombMap.sigma ^ (N - q)) (X.toCombMap.alpha d₀) = I.y ∧
      (∀ i j, i < N → j < N → (X.toCombMap.sigma ^ i) (X.toCombMap.alpha d₀) =
        (X.toCombMap.sigma ^ j) (X.toCombMap.alpha d₀) → i = j) ∧
      (∀ z, RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ z →
        ∃ p, 0 < p ∧ p < k₀ ∧ (X.toCombMap.sigma ^ p) (X.toCombMap.alpha d₀) = z) ∧
      ∀ z, walkKeep X.toCombMap c z →
        X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) z →
          z ≠ X.toCombMap.alpha d₀ → z ≠ e₀ →
            ¬ RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ z →
              ∃ p, m + k₀ < p ∧ p ≤ N - q ∧ (X.toCombMap.sigma ^ p) (X.toCombMap.alpha d₀) = z := by
  obtain ⟨N, hN⟩ : ∃ N, Function.minimalPeriod X.toCombMap.sigma (X.toCombMap.alpha d₀) = N :=
    ⟨_, rfl⟩
  have hpos : 0 < N := by
    rw [← hN]
    exact minimalPeriod_pos _ _
  have hper : (X.toCombMap.sigma ^ N) (X.toCombMap.alpha d₀) = X.toCombMap.alpha d₀ := by
    rw [← hN]
    exact pow_minimalPeriod_apply _ _
  have hinj : ∀ i j, i < N → j < N → (X.toCombMap.sigma ^ i) (X.toCombMap.alpha d₀) =
      (X.toCombMap.sigma ^ j) (X.toCombMap.alpha d₀) → i = j := fun i j hi hj h =>
    pow_eq_pow_below (by rw [hN]; exact hi) (by rw [hN]; exact hj) h
  have hkeepα : walkKeep X.toCombMap c (X.toCombMap.alpha d₀) :=
    Or.inr (by rw [X.toCombMap.alpha_involutive]; exact hd₀)
  have hk₀pos : 0 < k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h0 | h0
    · rw [h0, pow_zero, Equiv.Perm.one_apply] at hk₀
      exact absurd (by rw [hk₀]; exact he₀) (hc d₀ hd₀)
    · exact h0
  -- `e₀` is first reached before the minimal period.
  have hk₀N : k₀ < N := by
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hlt | heq
    · refine hk₀min (k₀ - N) (Nat.sub_pos_of_lt hlt) (by omega) ?_
      have h1 := hk₀
      rwa [← Nat.sub_add_cancel hlt.le, pow_add_apply, hper] at h1
    · rw [← heq, hper] at hk₀
      exact hc d₀ hd₀ (by rw [hk₀]; exact he₀)
  have hxpos : (X.toCombMap.sigma ^ (m + k₀)) (X.toCombMap.alpha d₀) = I.x := by
    rw [pow_add_apply, hk₀, hm]
  -- `y` is a period of rotation, and it sits at position `N - q`.
  have hyper : (X.toCombMap.sigma ^ N) I.y = I.y := by
    apply (X.toCombMap.sigma ^ q).injective
    rw [← Equiv.Perm.mul_apply, pow_mul_comm, Equiv.Perm.mul_apply, hq, hper]
  have hqN : q ≤ N := by
    by_contra hlt
    push Not at hlt
    refine hkeepq (q - N) (Nat.sub_pos_of_lt hlt) (by omega) ?_
    have h1 : (X.toCombMap.sigma ^ (q - N)) I.y = X.toCombMap.alpha d₀ := by
      rw [← hyper, ← pow_add_apply, Nat.sub_add_cancel hlt.le, hq]
    rw [h1]
    exact hkeepα
  have hypos : (X.toCombMap.sigma ^ (N - q)) (X.toCombMap.alpha d₀) = I.y := by
    rw [← hq, ← pow_add_apply, Nat.sub_add_cancel hqN, hyper]
  -- Positions after `y` hold no dart on an edge of the cycle.
  have hbeyond : ∀ p, N - q < p → p < N →
      ¬ walkKeep X.toCombMap c ((X.toCombMap.sigma ^ p) (X.toCombMap.alpha d₀)) := by
    intro p hp hpN hk
    refine hkeepq (p - (N - q)) (Nat.sub_pos_of_lt hp) (by omega) ?_
    have h1 : (X.toCombMap.sigma ^ (p - (N - q))) I.y =
        (X.toCombMap.sigma ^ p) (X.toCombMap.alpha d₀) := by
      rw [← hypos, ← pow_add_apply, Nat.sub_add_cancel hp.le]
    rw [h1]
    exact hk
  have hinside : ∀ z, RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ z →
      ∃ p, 0 < p ∧ p < k₀ ∧ (X.toCombMap.sigma ^ p) (X.toCombMap.alpha d₀) = z := by
    rintro z ⟨p, hp, hpz, hpe⟩
    refine ⟨p, hp, ?_, hpz⟩
    by_contra hge
    push Not at hge
    exact hpe k₀ hk₀pos hge hk₀
  -- Every other keep dart outside the stretch comes after `x` and no later than `y`.
  have hafter : ∀ z, walkKeep X.toCombMap c z →
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) z →
        z ≠ X.toCombMap.alpha d₀ → z ≠ e₀ →
          ¬ RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ z →
            ∃ p, m + k₀ < p ∧ p ≤ N - q ∧ (X.toCombMap.sigma ^ p) (X.toCombMap.alpha d₀) = z := by
    intro z hz hzv hza hze hzout
    obtain ⟨p, hpN, hp⟩ := exists_pow_lt_of_sameCycle hzv
    rw [hN] at hpN
    refine ⟨p, ?_, ?_, hp⟩
    · by_contra hle
      push Not at hle
      rcases Nat.lt_trichotomy p k₀ with hlt | heq | hgt
      · rcases Nat.eq_zero_or_pos p with h0 | hp0
        · rw [h0, pow_zero, Equiv.Perm.one_apply] at hp
          exact hza hp.symm
        · exact hzout ⟨p, hp0, hp, fun b hb hbp => hk₀min b hb (by omega)⟩
      · rw [heq, hk₀] at hp
        exact hze hp.symm
      · refine hkeepm (p - k₀) (Nat.sub_pos_of_lt hgt) (by omega) ?_
        have h1 : (X.toCombMap.sigma ^ (p - k₀)) e₀ = z := by
          rw [← hk₀, ← pow_add_apply, Nat.sub_add_cancel hgt.le, hp]
        rw [h1]
        exact hz
    · by_contra hgt
      push Not at hgt
      exact hbeyond p hgt hpN (by rw [hp]; exact hz)
  obtain ⟨p₀, hp₀, hp₀N, -⟩ := hafter z₀ hz₀ hz₀v hz₀a hz₀e hz₀out
  exact ⟨N, hpos, hk₀N, hqN, by omega, hxpos, hypos, hinj, hinside, hafter⟩

/-- **Every turn is kept at the split of an uncrossed turn.**  The turn itself and the passages
strictly inside its stretch run into `x` without passing `y`; the other passages at the vertex run
into `y` without passing `x`; a turn at another vertex never meets the split darts. -/
theorem chordKept_of_uncrossed (I : PinchSplit.Input X) (hne : c ≠ []) (hnodup : c.Nodup)
    (hc : ∀ d ∈ c, X.toCombMap.alpha d ∉ c)
    (hchain : c.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e)
    (hcloses : X.toCombMap.vertexOf (X.toCombMap.alpha (c.getLast hne)) =
      X.toCombMap.vertexOf (c.head hne))
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ c) (hnext₀ : c.next d₀ hd₀ = e₀)
    (huncross : ∀ d (hd : d ∈ c), d ≠ d₀ →
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) →
        (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (c.next d hd)))
    {k₀ m q : ℕ} (hk₀ : (X.toCombMap.sigma ^ k₀) (X.toCombMap.alpha d₀) = e₀)
    (hk₀min : ∀ t, 0 < t → t < k₀ → (X.toCombMap.sigma ^ t) (X.toCombMap.alpha d₀) ≠ e₀)
    (hm : (X.toCombMap.sigma ^ m) e₀ = I.x)
    (hkeepm : ∀ t, 0 < t → t ≤ m → ¬ walkKeep X.toCombMap c ((X.toCombMap.sigma ^ t) e₀))
    (hq0 : 0 < q) (hq : (X.toCombMap.sigma ^ q) I.y = X.toCombMap.alpha d₀)
    (hkeepq : ∀ t, 0 < t → t < q → ¬ walkKeep X.toCombMap c ((X.toCombMap.sigma ^ t) I.y))
    {z₀ : X.toCombMap.Dart} (hz₀ : z₀ ∈ c)
    (hz₀v : X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) z₀) (hz₀e : z₀ ≠ e₀)
    (hz₀out : ¬ RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ z₀)
    {d : X.toCombMap.Dart} (hd : d ∈ c) :
    I.ChordKept (X.toCombMap.alpha d) (c.next d hd) := by
  have he₀ : e₀ ∈ c := by
    rw [← hnext₀]
    exact List.next_mem ..
  have hz₀a : z₀ ≠ X.toCombMap.alpha d₀ := fun h => hc d₀ hd₀ (by rw [← h]; exact hz₀)
  obtain ⟨N, -, -, -, hmk, hxpos, hypos, hinj, hinside, hafter⟩ := chord_positions I hc hd₀ he₀
    hk₀ hk₀min hm hkeepm hq hkeepq (Or.inl hz₀) hz₀v hz₀a hz₀e hz₀out
  have hprev : ∀ (a b : X.toCombMap.Dart) (ha : a ∈ c) (hb : b ∈ c),
      a = b → c.prev a ha = c.prev b hb := by
    rintro a b ha hb rfl
    rfl
  by_cases hdd : d = d₀
  · subst hdd
    rw [hnext₀]
    exact Or.inr ⟨runsIntoX_of_pos hinj hq0 hmk hxpos hypos (Nat.zero_le _)
        (by rw [pow_zero, Equiv.Perm.one_apply]),
      runsIntoX_of_pos hinj hq0 hmk hxpos hypos (Nat.le_add_left _ _) hk₀⟩
  · have hemem : c.next d hd ∈ c := List.next_mem ..
    have hvert : X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf (c.next d hd) :=
      rel_next_of_isChain hne hnodup hchain hcloses hd
    have hsame : X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d) (c.next d hd) :=
      (X.toCombMap.vertexOf_eq_iff _ _).mp hvert
    by_cases hv : X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d)
    · have hαd : walkKeep X.toCombMap c (X.toCombMap.alpha d) :=
        Or.inr (by rw [X.toCombMap.alpha_involutive]; exact hd)
      have hαne₀ : X.toCombMap.alpha d ≠ X.toCombMap.alpha d₀ := fun h =>
        hdd (X.toCombMap.alpha.injective h)
      have hαe₀ : X.toCombMap.alpha d ≠ e₀ := fun h => hc d hd (by rw [h]; exact he₀)
      have hnα : c.next d hd ≠ X.toCombMap.alpha d₀ := fun h =>
        hc d₀ hd₀ (by rw [← h]; exact hemem)
      have hne₀ : c.next d hd ≠ e₀ := fun h =>
        hdd (((List.prev_next c hnodup d hd).symm.trans
          (hprev _ _ _ _ (h.trans hnext₀.symm))).trans (List.prev_next c hnodup d₀ hd₀))
      by_cases hin : RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (X.toCombMap.alpha d)
      · obtain ⟨p₁, -, hp₁, hz₁⟩ := hinside _ hin
        obtain ⟨p₂, -, hp₂, hz₂⟩ := hinside _ ((huncross d hd hdd hv).mp hin)
        exact Or.inr ⟨runsIntoX_of_pos hinj hq0 hmk hxpos hypos (by omega) hz₁,
          runsIntoX_of_pos hinj hq0 hmk hxpos hypos (by omega) hz₂⟩
      · have hin' : ¬ RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (c.next d hd) :=
          fun h => hin ((huncross d hd hdd hv).mpr h)
        obtain ⟨p₁, hp₁, hp₁N, hz₁⟩ := hafter _ hαd hv hαne₀ hαe₀ hin
        obtain ⟨p₂, hp₂, hp₂N, hz₂⟩ := hafter _ (Or.inl hemem) (hv.trans hsame) hnα hne₀ hin'
        exact Or.inl (Or.inr ⟨runsIntoY_of_pos hinj hq0 hxpos hypos hp₁ hp₁N hz₁,
          runsIntoY_of_pos hinj hq0 hxpos hypos hp₂ hp₂N hz₂⟩)
    · obtain ⟨n, hn⟩ := hsame.exists_nat_pow_eq
      refine Or.inl (Or.inl ⟨n, hn, fun i _ => ⟨fun hx => hv ?_, fun hy' => hv ?_⟩⟩)
      · exact (sameCycle_of_pow_eq hxpos).trans (sameCycle_of_pow_eq hx).symm
      · exact (sameCycle_of_pow_eq hypos).trans (sameCycle_of_pow_eq hy').symm

end Walk

end OuterPinchChord

open OuterPinchIsolated OuterPinchChord

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Walk order across a split at an uncrossed turn**: every turn of the cycle, and the closing
turn, is kept at the split. -/
theorem pinchSplit_closedWalk_of_chordKept (K : PocketFaceSet D eps X lo hi)
    (I : PinchSplit.Input X) (hs : I.Avoids K.faces)
    (hchain : K.boundary.cycle.IsChain fun d e => I.ChordKept (X.toCombMap.alpha d) e)
    (hcloses : I.ChordKept
      (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))
      (K.boundary.cycle.head K.boundary.cycle_nonempty)) :
    (K.pinchSplit I hs).ClosedWalk :=
  ⟨hchain.imp fun _ _ h => I.vertexOf_eq_of_chordKept h, I.vertexOf_eq_of_chordKept hcloses⟩

/-- **One step of the section pinch under the kept-turn chain of an uncrossed turn.** -/
theorem exists_pinchStepSection_of_chordKept
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : PocketFaceSet D eps X lo hi)
    (hprop : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    (I : PinchSplit.Input X) (hs : I.Avoids K.faces)
    (hchain : K.boundary.cycle.IsChain fun d e => I.ChordKept (X.toCombMap.alpha d) e)
    (hcloses : I.ChordKept
      (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))
      (K.boundary.cycle.head K.boundary.cycle_nonempty))
    {e₁ e₂ : X.toCombMap.Dart} (he₁ : e₁ ∈ K.boundary.cycle) (he₂ : e₂ ∈ K.boundary.cycle)
    {n₁ n₂ : ℕ} (hn₁ : (X.toCombMap.sigma ^ n₁) e₁ = I.x)
    (hy₁ : ∀ i ≤ n₁, (X.toCombMap.sigma ^ i) e₁ ≠ I.y)
    (hn₂ : (X.toCombMap.sigma ^ n₂) e₂ = I.y)
    (hx₂ : ∀ i ≤ n₂, (X.toCombMap.sigma ^ i) e₂ ≠ I.x) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
        K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
        K'.targetArc.length < (outerDarts X').length ∧
        K'.repeatedVisits < K.repeatedVisits :=
  ⟨I.diagram, K.pinchSplit I hs, ⟨I.oEquivalent⟩,
    I.label_isLetter (symmetricLabelAlphabet D) hlabel,
    K.pinchSplit_closedWalk_of_chordKept I hs hchain hcloses, K.pinchSplit_source_proper I hs hprop,
    K.pinchSplit_target_proper I hs htgt,
    K.pinchSplit_repeatedVisits_lt_of_stretch I hs he₁ he₂ hn₁ hy₁ hn₂ hx₂⟩

/-- **One step of the section pinch at an uncrossed turn.**  For a pocket in walk order with both
arcs proper, a split outside the face set at a turn `d₀ → e₀` that no other passage at its vertex
crosses, with `x` reached from `e₀` and `alpha d₀` reached from `y` past darts off the edges of the
cycle, and a dart `z₀` of the cycle at the vertex outside the stretch from `alpha d₀` to `e₀`, gives
the conclusion of the step with both proper arcs. -/
theorem exists_pinchStepSection_of_uncrossedTurn
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hprop : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    (I : PinchSplit.Input X) (hs : I.Avoids K.faces)
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (hnext₀ : K.boundary.cycle.next d₀ hd₀ = e₀)
    (huncross : ∀ d (hd : d ∈ K.boundary.cycle), d ≠ d₀ →
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) →
        (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (K.boundary.cycle.next d hd)))
    {k₀ m q : ℕ} (hk₀ : (X.toCombMap.sigma ^ k₀) (X.toCombMap.alpha d₀) = e₀)
    (hk₀min : ∀ t, 0 < t → t < k₀ → (X.toCombMap.sigma ^ t) (X.toCombMap.alpha d₀) ≠ e₀)
    (hm : (X.toCombMap.sigma ^ m) e₀ = I.x)
    (hkeepm : ∀ t, 0 < t → t ≤ m →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) e₀))
    (hq0 : 0 < q) (hq : (X.toCombMap.sigma ^ q) I.y = X.toCombMap.alpha d₀)
    (hkeepq : ∀ t, 0 < t → t < q →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) I.y))
    {z₀ : X.toCombMap.Dart} (hz₀ : z₀ ∈ K.boundary.cycle)
    (hz₀v : X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) z₀) (hz₀e : z₀ ≠ e₀)
    (hz₀out : ¬ RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ z₀) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
        K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
        K'.targetArc.length < (outerDarts X').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  have hc : ∀ d ∈ K.boundary.cycle, X.toCombMap.alpha d ∉ K.boundary.cycle :=
    fun d hd => K.boundary_alpha_not_mem hd
  have he₀ : e₀ ∈ K.boundary.cycle := by
    rw [← hnext₀]
    exact List.next_mem ..
  have hz₀a : z₀ ≠ X.toCombMap.alpha d₀ := fun h => hc d₀ hd₀ (by rw [← h]; exact hz₀)
  obtain ⟨N, -, -, -, hmk, hxpos, hypos, hinj, -, hafter⟩ := chord_positions I hc hd₀ he₀ hk₀
    hk₀min hm hkeepm hq hkeepq (Or.inl hz₀) hz₀v hz₀a hz₀e hz₀out
  obtain ⟨hchain, hcloses⟩ := isChain_of_rel_next K.boundary.cycle_nonempty K.boundary.cycle_nodup
    (R := fun d e => I.ChordKept (X.toCombMap.alpha d) e)
    fun d hd => chordKept_of_uncrossed I K.boundary.cycle_nonempty K.boundary.cycle_nodup hc hK.1
      hK.2 hd₀ hnext₀ huncross hk₀ hk₀min hm hkeepm hq0 hq hkeepq hz₀ hz₀v hz₀e hz₀out hd
  obtain ⟨p, hp, hpN, hz⟩ := hafter z₀ (Or.inl hz₀) hz₀v hz₀a hz₀e hz₀out
  obtain ⟨n₂, hn₂, hx₂⟩ := runsIntoY_of_pos hinj hq0 hxpos hypos hp hpN hz
  obtain ⟨n₁, hn₁, hy₁⟩ := runsIntoX_of_pos hinj hq0 hmk hxpos hypos (Nat.le_add_left _ _) hk₀
  exact K.exists_pinchStepSection_of_chordKept hlabel hprop htgt I hs hchain hcloses he₀ hz₀ hn₁
    hy₁ hn₂ hx₂

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.ChordKept
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.vertexOf_eq_of_chordKept
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchChord.runsIntoX_of_pos
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchChord.runsIntoY_of_pos
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchChord.chord_positions
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchChord.chordKept_of_uncrossed
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_closedWalk_of_chordKept
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.exists_pinchStepSection_of_chordKept
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.exists_pinchStepSection_of_uncrossedTurn
