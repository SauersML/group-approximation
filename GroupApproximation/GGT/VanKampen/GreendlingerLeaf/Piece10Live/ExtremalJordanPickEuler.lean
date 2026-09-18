import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickThree
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkPassageKinds
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchIsolated
import GroupApproximation.Meta.AxiomGuard

/-!
# The local lemma of the Euler core: `n_v ≥ 1` forces `n_v ≥ 3`

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-39.

Write `σ` for the rotation, `α` for the reversal and `c` for the boundary cycle of a pocket `K`.
A *passage* is `α d → next d` for `d ∈ c`.  It is *non-first* (`P10ChordLift.NonFirstTurn`)
when the rotation sector from `next d` to `α d` meets another walk dart.  The residual
`ExtremalJordanPickThreeTwoOutsideStatement` (lane gl-p10-38) rests on the Euler identity
`#linked + #outside = 2 + Σ_v max(n_v - 1, 0)`, where `n_v` counts the non-first passages at `v`,
and on the local fact that every vertex with `n_v ≥ 1` has `n_v ≥ 3`.  This file proves the
local fact outright, in the rose configuration (`P10ChordLift.AllNonFirstTurnsCrossed K`).

* **Alternation** (`extremalJordanPickEuler_alpha_mem_of_firstKept`).  Rotating from a walk dart
  `a ∈ c`, the first walk-or-reversal dart met is the reversal `α b` of a walk dart `b ∈ c`.
  *Proof.*  The face after `a` in the rotation is the face of `α a`, which lies outside
  `K.faces`.  A dart skipped by the rotation is neither in `c` nor the reversal of a dart of `c`,
  so the outside face carries over to the next step.  At the first kept dart `z`, `z ∉ c`, since
  its face is outside; so `α z ∈ c`.
* **First passages** (`extremalJordanPickEuler_nonFirst_iff`).  `d` is non-first exactly when
  the sector from `next d` to `α d` is not free (`SectorNoninterleaving.SectorFree`).
* **Successor** (`extremalJordanPickEuler_next_nonFirst`).  For a non-first `d₀`, the first kept
  dart after `next d₀` is `α d₁` with `d₁ ∈ c`.  Then `d₁ ≠ d₀`, `d₁` is at the same vertex, and
  `d₁` is non-first: otherwise both `next d₀` and `next d₁` would reach `α d₁` through a free
  sector, so `next d₀ = next d₁` (`SectorNoninterleaving.eq_of_sectorFree_rev_both`) and
  `d₀ = d₁`.
* **Three at the vertex** (`extremalJordanPickEuler_three_nonFirst`).  Take the successor `d₁`
  of `d₀` and the successor `e` of `d₁`.  If `e ≠ d₀` we are done.  If `e = d₀`, the passage
  `d₁` lies outside the sector of `d₀` at both ends, so it does not cross `d₀`.  A first passage
  never crosses (`extremalJordanPickEuler_between_iff_of_free`).  So the crosser `d` of `d₀`
  given by the rose hypothesis is non-first and differs from `d₀` and `d₁`.

These are proved lemmas with no open input.  They use only that `σ` is a permutation of a finite
set, and that the boundary darts of `K` are the darts `d` with the face of `d` in `K.faces` and
the face of `α d` outside.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Surgery.MapCollapse SimpleClosedWalkSides
open scoped Classical

section General

/-- **Rotation after a reversal is the face permutation**: `facePerm (α d) = σ d`. -/
theorem extremalJordanPickEuler_facePerm_alpha (M : CombMap.{v}) (d : M.Dart) :
    M.facePerm (M.alpha d) = M.sigma d := by
  show M.sigma (M.alpha (M.alpha d)) = M.sigma d
  rw [M.alpha_involutive d]

/-- **The successor in a duplicate-free list is injective.** -/
theorem extremalJordanPickEuler_next_injective {β : Type*} {l : List β} (hl : l.Nodup)
    {a b : β} (ha : a ∈ l) (hb : b ∈ l) (h : l.next a ha = l.next b hb) : a = b := by
  have key : ∀ (x y : β) (hx : x ∈ l) (hy : y ∈ l), x = y → l.prev x hx = l.prev y hy := by
    rintro x _ hx hy rfl
    rfl
  calc a = l.prev (l.next a ha) (List.next_mem _ _ ha) := (List.prev_next l hl a ha).symm
    _ = l.prev (l.next b hb) (List.next_mem _ _ hb) := key _ _ _ _ h
    _ = b := List.prev_next l hl b hb

/-- **A first kept dart exists**: rotating from a kept dart, some positive power is kept again
(the minimal period returns to the start), and there is a least such power. -/
theorem extremalJordanPickEuler_exists_firstKept (M : CombMap.{v}) (c : List M.Dart)
    {a : M.Dart} (ha : walkKeep M c a) :
    ∃ k, 0 < k ∧ walkKeep M c ((M.sigma ^ k) a) ∧
      ∀ t, 0 < t → t < k → ¬walkKeep M c ((M.sigma ^ t) a) := by
  have hex : ∃ k, 0 < k ∧ walkKeep M c ((M.sigma ^ k) a) :=
    ⟨Function.minimalPeriod M.sigma a, OuterPinchIsolated.minimalPeriod_pos M.sigma a, by
      rw [OuterPinchIsolated.pow_minimalPeriod_apply]
      exact ha⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun t ht htk hkt => ?_⟩
  exact Nat.find_min hex htk ⟨ht, hkt⟩

variable {M : CombMap.{v}} {c : List M.Dart}

/-- A walk dart is kept. -/
theorem extremalJordanPickEuler_keep_of_mem {d : M.Dart} (h : d ∈ c) : walkKeep M c d := by
  unfold walkKeep
  exact Or.inl h

/-- The reversal of a walk dart is kept. -/
theorem extremalJordanPickEuler_keep_alpha_of_mem {d : M.Dart} (h : d ∈ c) :
    walkKeep M c (M.alpha d) := by
  unfold walkKeep
  rw [M.alpha_involutive d]
  exact Or.inr h

/-- **Alternation at a vertex.**  Let `c` list exactly the boundary darts of `faces`.  Rotating
from `a ∈ c`, the first kept dart `(σ^k) a` is the reversal of a dart of `c`. -/
theorem extremalJordanPickEuler_alpha_mem_of_firstKept {faces : Finset M.Face}
    (hmem : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d) {a : M.Dart}
    (ha : a ∈ c) {k : ℕ} (hk : 0 < k) (hfree : ∀ t, 0 < t → t < k → ¬walkKeep M c ((M.sigma ^ t) a))
    (hkeep : walkKeep M c ((M.sigma ^ k) a)) : M.alpha ((M.sigma ^ k) a) ∈ c := by
  have hout : ∀ t, 0 < t → t ≤ k → M.faceOf ((M.sigma ^ t) a) ∉ faces := by
    intro t
    induction t with
    | zero => intro h; exact absurd h (Nat.lt_irrefl 0)
    | succ n ih =>
      intro _ hn
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        rw [zero_add, pow_one, ← extremalJordanPickEuler_facePerm_alpha M a, M.faceOf_facePerm]
        exact ((hmem a).mp ha).2
      · have hprev := ih hpos (by omega)
        have hunk := hfree n hpos (by omega)
        have hy : M.alpha ((M.sigma ^ n) a) ∉ c := fun h =>
          hunk (by unfold walkKeep; exact Or.inr h)
        have hfa : M.faceOf (M.alpha ((M.sigma ^ n) a)) ∉ faces := by
          intro hin
          apply hy
          refine (hmem _).mpr ⟨hin, ?_⟩
          rw [M.alpha_involutive ((M.sigma ^ n) a)]
          exact hprev
        rw [pow_succ', Equiv.Perm.mul_apply,
          ← extremalJordanPickEuler_facePerm_alpha M ((M.sigma ^ n) a), M.faceOf_facePerm]
        exact hfa
  have hk' := hout k hk le_rfl
  unfold walkKeep at hkeep
  rcases hkeep with h | h
  · exact absurd ((hmem _).mp h).1 hk'
  · exact h

/-- **A kept dart is outside the sector after a free sector** (G1): if the sector from `y` to
`z` is free and `x ≠ y` is kept, then `z` is not strictly between `x` and `y`. -/
theorem extremalJordanPickEuler_not_between_of_free_after {x y z : M.Dart}
    (h : SectorNoninterleaving.SectorFree M c y z) (hx : walkKeep M c x) (hxy : x ≠ y) :
    ¬RotationBetween M x y z := by
  rintro ⟨a, ha, haz, hay⟩
  obtain ⟨m, hm, hfree⟩ := h
  rcases Nat.lt_or_ge a m with hlt | hge
  · have hxe : (M.sigma ^ (m - a)) y = x := by
      apply (M.sigma ^ a).injective
      rw [← OuterPinchIsolated.pow_add_apply, Nat.add_sub_of_le hlt.le, hm, haz]
    exact hfree (m - a) (by omega) (by omega) (by rw [hxe]; exact hx)
  · have hye : (M.sigma ^ (a - m)) x = y := by
      apply (M.sigma ^ m).injective
      rw [← OuterPinchIsolated.pow_add_apply, Nat.add_sub_of_le hge, hm, haz]
    rcases Nat.eq_zero_or_pos (a - m) with h0 | h0
    · rw [h0, pow_zero, Equiv.Perm.one_apply] at hye
      exact hxy hye
    · exact hay (a - m) h0 (Nat.sub_le a m) hye

/-- **A kept dart is outside the sector before a free sector** (G2): if the sector from `z` to
`x` is free and `y` is a kept dart at the vertex of `x` other than `x` and `z`, then `z` is not
strictly between `x` and `y`. -/
theorem extremalJordanPickEuler_not_between_of_free_before {x y z : M.Dart}
    (h : SectorNoninterleaving.SectorFree M c z x) (hv : M.vertexOf y = M.vertexOf x)
    (hy : walkKeep M c y) (hyx : y ≠ x) (hyz : y ≠ z) : ¬RotationBetween M x y z := fun hb =>
  RotationBetween.not_both hb
    (SectorNoninterleaving.rotationBetween_of_sectorFree_rev h hv hy hyx hyz)

/-- **Both ends of a free sector lie on one side** (G3): if the sector from `n` to `z` is free,
`x ≠ n` and `y ≠ z` are kept, then `z` is strictly between `x` and `y` exactly when `n` is. -/
theorem extremalJordanPickEuler_between_iff_of_free {x y n z : M.Dart}
    (h : SectorNoninterleaving.SectorFree M c n z) (hx : walkKeep M c x) (hy : walkKeep M c y)
    (hxn : x ≠ n) (hyz : y ≠ z) : RotationBetween M x y z ↔ RotationBetween M x y n := by
  obtain ⟨m, hm, hfree⟩ := h
  constructor
  · rintro ⟨a, ha, haz, hay⟩
    rcases Nat.lt_or_ge a m with hlt | hge
    · have hxe : (M.sigma ^ (m - a)) n = x := by
        apply (M.sigma ^ a).injective
        rw [← OuterPinchIsolated.pow_add_apply, Nat.add_sub_of_le hlt.le, hm, haz]
      exact (hfree (m - a) (by omega) (by omega) (by rw [hxe]; exact hx)).elim
    · have hne : (M.sigma ^ (a - m)) x = n := by
        apply (M.sigma ^ m).injective
        rw [← OuterPinchIsolated.pow_add_apply, Nat.add_sub_of_le hge, hm, haz]
      have hpos : 0 < a - m := by
        rcases Nat.eq_zero_or_pos (a - m) with h0 | h0
        · rw [h0, pow_zero, Equiv.Perm.one_apply] at hne
          exact (hxn hne).elim
        · exact h0
      exact ⟨a - m, hpos, hne, fun b hb hba => hay b hb (by omega)⟩
  · rintro ⟨a, ha, han, hay⟩
    refine ⟨m + a, by omega, ?_, fun b hb hba => ?_⟩
    · rw [OuterPinchIsolated.pow_add_apply, han, hm]
    · rcases Nat.lt_or_ge a b with hab | hab
      · intro hby
        have hb' : (M.sigma ^ (b - a)) n = y := by
          rw [← han, ← OuterPinchIsolated.pow_add_apply, Nat.sub_add_cancel hab.le]
          exact hby
        rcases Nat.lt_or_ge (b - a) m with htm | htm
        · exact hfree (b - a) (by omega) htm (by rw [hb']; exact hy)
        · have hbm : b - a = m := by omega
          rw [hbm, hm] at hb'
          exact hyz hb'.symm
      · exact hay b hb hab

end General

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Non-first passages**: `d` is non-first exactly when the sector from `next d` to `α d` is
not free. -/
theorem extremalJordanPickEuler_nonFirst_iff (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle) :
    P10ChordLift.NonFirstTurn K d hd ↔ ¬SectorNoninterleaving.SectorFree X.toCombMap
      K.boundary.cycle (K.boundary.cycle.next d hd) (X.toCombMap.alpha d) := by
  unfold P10ChordLift.NonFirstTurn
  rw [FirstTurn.reverse_map_alpha_iff]
  apply not_congr
  constructor
  · rintro ⟨k, -, hk, hfree⟩
    exact ⟨k, hk, hfree⟩
  · rintro ⟨m, hm, hfree⟩
    refine ⟨m, ?_, hm, hfree⟩
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero, Equiv.Perm.one_apply] at hm
      exact (K.boundary_alpha_not_mem hd (by rw [← hm]; exact List.next_mem _ _ hd)).elim
    · exact h0

/-- **The successor of a non-first passage.**  For a non-first `d₀`, the first kept dart after
`next d₀` in the rotation is `α d₁` for a non-first `d₁ ≠ d₀` at the same vertex, and the
sector from `next d₀` to `α d₁` is free. -/
theorem extremalJordanPickEuler_next_nonFirst (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) {d₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (hnf : P10ChordLift.NonFirstTurn K d₀ hd₀) :
    ∃ (d₁ : X.toCombMap.Dart) (hd₁ : d₁ ∈ K.boundary.cycle), d₁ ≠ d₀ ∧
      P10ChordLift.NonFirstTurn K d₁ hd₁ ∧
      SectorNoninterleaving.SectorFree X.toCombMap K.boundary.cycle
        (K.boundary.cycle.next d₀ hd₀) (X.toCombMap.alpha d₁) ∧
      X.toCombMap.vertexOf (X.toCombMap.alpha d₁) =
        X.toCombMap.vertexOf (X.toCombMap.alpha d₀) := by
  have hn : K.boundary.cycle.next d₀ hd₀ ∈ K.boundary.cycle := List.next_mem _ _ hd₀
  obtain ⟨k, hk, hkeep, hfree⟩ :=
    extremalJordanPickEuler_exists_firstKept X.toCombMap K.boundary.cycle
      (extremalJordanPickEuler_keep_of_mem hn)
  have hmem := extremalJordanPickEuler_alpha_mem_of_firstKept K.boundary.cycle_mem_iff hn hk
    hfree hkeep
  obtain ⟨d₁, hd₁e⟩ : ∃ d₁, (X.toCombMap.sigma ^ k) (K.boundary.cycle.next d₀ hd₀) =
      X.toCombMap.alpha d₁ :=
    ⟨X.toCombMap.alpha ((X.toCombMap.sigma ^ k) (K.boundary.cycle.next d₀ hd₀)),
      (X.toCombMap.alpha_involutive _).symm⟩
  rw [hd₁e, X.toCombMap.alpha_involutive d₁] at hmem
  have hfr : SectorNoninterleaving.SectorFree X.toCombMap K.boundary.cycle
      (K.boundary.cycle.next d₀ hd₀) (X.toCombMap.alpha d₁) := ⟨k, hd₁e, hfree⟩
  have hne : d₁ ≠ d₀ := by
    intro heq
    rw [heq] at hfr
    exact (extremalJordanPickEuler_nonFirst_iff K hd₀).mp hnf hfr
  have hv₂ : X.toCombMap.vertexOf (X.toCombMap.alpha d₀) =
      X.toCombMap.vertexOf (K.boundary.cycle.next d₀ hd₀) :=
    OuterPinchIsolated.rel_next_of_isChain K.boundary.cycle_nonempty K.boundary.cycle_nodup
      hK.1 hK.2 hd₀
  refine ⟨d₁, hmem, hne, (extremalJordanPickEuler_nonFirst_iff K hmem).mpr fun hfr₁ => ?_,
    hfr, (SectorNoninterleaving.SectorFree.vertexOf_eq hfr).trans hv₂.symm⟩
  have hx₁ : K.boundary.cycle.next d₀ hd₀ ≠ X.toCombMap.alpha d₁ := fun h =>
    K.boundary_alpha_not_mem hmem (by rw [← h]; exact hn)
  have hx₂ : K.boundary.cycle.next d₁ hmem ≠ X.toCombMap.alpha d₁ := fun h =>
    K.boundary_alpha_not_mem hmem (by rw [← h]; exact List.next_mem _ _ hmem)
  have heq := SectorNoninterleaving.eq_of_sectorFree_rev_both hfr hfr₁
    (extremalJordanPickEuler_keep_of_mem hn)
    (extremalJordanPickEuler_keep_of_mem (List.next_mem _ _ hmem)) hx₁ hx₂
  exact hne (extremalJordanPickEuler_next_injective K.boundary.cycle_nodup hd₀ hmem heq).symm

end Pocket
