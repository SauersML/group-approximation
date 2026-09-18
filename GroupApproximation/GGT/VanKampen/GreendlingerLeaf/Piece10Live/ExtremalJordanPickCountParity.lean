import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCount
import GroupApproximation.Meta.AxiomGuard

/-!
# The parity clause: the sign argument

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-43.

`ExtremalJordanPickCountParity K` (lane gl-p10-41) says `excess = 2 → #O ≠ 2`.  This file proves
it from one comparison of a class count with an orbit count.

**The sign argument.**  Let `c` be the walk and `m` its length.  Let `f` be a permutation of the
darts that fixes every dart off `c` and satisfies

  `f (next d) = d  ↔  d is a first passage`  for `d ∈ c`.

Put `h = f * formPerm c`.  Then `h d ≠ d` exactly for the non-first passages
(`extremalJordanPickCountParity_support_eq`).
* With `excess = 2` there are exactly three non-first passages
  (`extremalJordanPickCountParity_card_nonFirst`).  The proved local lemma
  `ExtremalJordanPickEulerThreeAtVertex` gives `n_x = 0 ∨ n_x ≥ 3` at every vertex.  So
  `2 Σ n_x ≤ 3 Σ (n_x - 1) = 6`, and some `n_x ≥ 3`.
* So `h` has support of size three.  It is a 3-cycle, with sign `1`.
* `formPerm c` is an `m`-cycle, with sign `-(-1)^m`.  So `sign f = -(-1)^m`.
* The number of orbits of `f` on `c` is `(m - #supp f) + #cycleType f`.  Its sign is
  `(-1)^(#supp f + #cycleType f) = sign f`.  So this number is odd
  (`extremalJordanPickCountParity_perm_odd`).

So if `#O` has the parity of the orbit count of `f` on `c`, then `#O` is odd and `#O ≠ 2`
(`extremalJordanPickCountParity_of_perm`).  The concrete `f` is `α ∘ σ_P` on the walk map
(`ExtremalJordanPickCountParityPerm.lean`).  The remaining class count is isolated in
`ExtremalJordanPickCountParityCycles.lean`.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

section ParityAbstract

/-- **Parity from signs**: equal powers of `-1` in `ℤˣ` have exponents of equal parity. -/
theorem extremalJordanPickCountParity_mod_two_eq {a b : ℕ}
    (h : (-1 : ℤˣ) ^ a = (-1) ^ b) : a % 2 = b % 2 := by
  rw [Int.units_pow_eq_pow_mod_two (-1) a, Int.units_pow_eq_pow_mod_two (-1) b] at h
  have hne : (1 : ℤˣ) ≠ -1 := units_ne_neg_self 1
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    rw [ha, hb] at h
  · omega
  · rw [pow_zero, pow_one] at h
    exact absurd h hne
  · rw [pow_zero, pow_one] at h
    exact absurd h.symm hne
  · omega

/-- **The sign argument.**  Let `f` fix every point off a duplicate-free list `l`.  If
`f * formPerm l` moves exactly three points, then the number of orbits of `f` on `l`, namely
`#l - #supp f + #cycleType f`, is odd. -/
theorem extremalJordanPickCountParity_perm_odd {α : Type*} [Fintype α] [DecidableEq α]
    (l : List α) (hl : l.Nodup) (f : Equiv.Perm α) (hf : ∀ x, x ∉ l → f x = x)
    (h3 : (f * l.formPerm).support.card = 3) :
    (l.length - f.support.card + f.cycleType.card) % 2 = 1 := by
  have hcard : l.toFinset.card = l.length := by
    rw [List.card_toFinset, List.dedup_eq_self.mpr hl]
  have hsubf : f.support ⊆ l.toFinset := by
    intro x hx
    rw [Equiv.Perm.mem_support] at hx
    rw [List.mem_toFinset]
    by_contra h
    exact hx (hf x h)
  have hsubh : (f * l.formPerm).support ⊆ l.toFinset := by
    intro x hx
    rw [Equiv.Perm.mem_support, Equiv.Perm.mul_apply] at hx
    rw [List.mem_toFinset]
    by_contra h
    exact hx (by rw [List.formPerm_apply_of_notMem h, hf x h])
  have hsf_le : f.support.card ≤ l.length := by
    have := Finset.card_le_card hsubf
    omega
  have h3le : 3 ≤ l.length := by
    have := Finset.card_le_card hsubh
    omega
  have hne : ∀ x, l ≠ [x] := by
    intro x hx
    rw [hx] at h3le
    simp at h3le
  have hform : Equiv.Perm.sign l.formPerm = -(-1) ^ l.length := by
    rw [(List.isCycle_formPerm hl (by omega)).sign, List.support_formPerm_of_nodup l hl hne,
      hcard]
  have hsh : Equiv.Perm.sign (f * l.formPerm) = 1 := (card_support_eq_three_iff.mp h3).sign
  rw [Equiv.Perm.sign_mul] at hsh
  have hsf : Equiv.Perm.sign f = Equiv.Perm.sign l.formPerm := by
    rw [eq_inv_of_mul_eq_one_left hsh, Int.units_inv_eq_self]
  have hpow : (-1 : ℤˣ) ^ (f.support.card + f.cycleType.card) = (-1) ^ (l.length + 1) := by
    rw [pow_succ (-1 : ℤˣ) l.length, mul_neg_one, ← hform, ← hsf,
      Equiv.Perm.sign_of_cycleType, Equiv.Perm.sum_cycleType]
  have := extremalJordanPickCountParity_mod_two_eq hpow
  omega

end ParityAbstract

section ParityPocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The non-first passages**: the walk darts `d` whose passage `d → next d` is not a first
turn. -/
noncomputable def extremalJordanPickCountParity_nonFirst (K : PocketFaceSet D eps X lo hi) :
    Finset X.toCombMap.Dart :=
  K.boundary.cycle.toFinset.filter fun d =>
    ∃ hd : d ∈ K.boundary.cycle, P10ChordLift.NonFirstTurn K d hd

/-- Membership in the non-first passages. -/
theorem extremalJordanPickCountParity_mem_nonFirst (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} :
    d ∈ extremalJordanPickCountParity_nonFirst K ↔
      ∃ hd : d ∈ K.boundary.cycle, P10ChordLift.NonFirstTurn K d hd := by
  unfold extremalJordanPickCountParity_nonFirst
  rw [Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨hd, hnf⟩
    exact ⟨hd, hd, hnf⟩

/-- **Three non-first passages**: with `excess = 2` there are exactly three non-first passages.
Each vertex has `n_x = 0` or `n_x ≥ 3`, so `2 Σ n_x ≤ 3 Σ (n_x - 1) = 6`, and some `n_x ≥ 3`. -/
theorem extremalJordanPickCountParity_card_nonFirst (K : PocketFaceSet D eps X lo hi)
    (h3 : ExtremalJordanPickEulerThreeAtVertex K) (hex : extremalJordanPickCount_excess K = 2) :
    (extremalJordanPickCountParity_nonFirst K).card = 3 := by
  have hmaps : ((extremalJordanPickCountParity_nonFirst K : Finset X.toCombMap.Dart) :
      Set X.toCombMap.Dart).MapsTo (fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d))
      (K.boundary.cycle.toFinset.image fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d)) := by
    intro d hd
    obtain ⟨hdc, -⟩ := (extremalJordanPickCountParity_mem_nonFirst K).mp (Finset.mem_coe.mp hd)
    exact Finset.mem_image.mpr ⟨d, List.mem_toFinset.mpr hdc, rfl⟩
  have hfib : (extremalJordanPickCountParity_nonFirst K).card =
      ∑ x ∈ K.boundary.cycle.toFinset.image
        (fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d)),
        extremalJordanPickCount_nonFirstAt K x := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold extremalJordanPickCount_nonFirstAt
    refine congrArg Finset.card (Finset.ext fun d => ?_)
    simp only [Finset.mem_filter, extremalJordanPickCountParity_mem_nonFirst, List.mem_toFinset]
    constructor
    · rintro ⟨⟨hd, hnf⟩, hv⟩
      exact ⟨hd, ⟨hd, hnf⟩, hv⟩
    · rintro ⟨-, h1, h2⟩
      exact ⟨h1, h2⟩
  have hdich : ∀ x ∈ K.boundary.cycle.toFinset.image
      (fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d)),
      extremalJordanPickCount_nonFirstAt K x = 0 ∨
        3 ≤ extremalJordanPickCount_nonFirstAt K x := by
    intro x _
    by_cases h0 : extremalJordanPickCount_nonFirstAt K x = 0
    · exact Or.inl h0
    · right
      have hpos : 0 < extremalJordanPickCount_nonFirstAt K x := Nat.pos_of_ne_zero h0
      unfold extremalJordanPickCount_nonFirstAt at hpos
      obtain ⟨d, hd⟩ := Finset.card_pos.mp hpos
      obtain ⟨-, ⟨hdc, hnf⟩, hv⟩ := Finset.mem_filter.mp hd
      have hlt := extremalJordanPickCount_two_lt_nonFirstAt K h3 hdc hnf
      rw [hv] at hlt
      omega
  have hup : 2 * ∑ x ∈ K.boundary.cycle.toFinset.image
        (fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d)),
        extremalJordanPickCount_nonFirstAt K x ≤
      3 * ∑ x ∈ K.boundary.cycle.toFinset.image
        (fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d)),
        (extremalJordanPickCount_nonFirstAt K x - 1) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun x hx => by rcases hdich x hx with h | h <;> omega
  unfold extremalJordanPickCount_excess at hex
  by_cases hall : ∀ x ∈ K.boundary.cycle.toFinset.image
      (fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d)),
      extremalJordanPickCount_nonFirstAt K x = 0
  · have hz : ∑ x ∈ K.boundary.cycle.toFinset.image
        (fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d)),
        (extremalJordanPickCount_nonFirstAt K x - 1) = 0 :=
      Finset.sum_eq_zero fun x hx => by
        have := hall x hx
        omega
    omega
  · push Not at hall
    obtain ⟨x, hx, hnx⟩ := hall
    have h3x := (hdich x hx).resolve_left hnx
    have hle : extremalJordanPickCount_nonFirstAt K x ≤
        ∑ y ∈ K.boundary.cycle.toFinset.image
          (fun d => X.toCombMap.vertexOf (X.toCombMap.alpha d)),
          extremalJordanPickCount_nonFirstAt K y :=
      Finset.single_le_sum (f := fun y => extremalJordanPickCount_nonFirstAt K y)
        (fun _ _ => Nat.zero_le _) hx
    omega

/-- **The return permutation moves the non-first passages.**  If `f` fixes the darts off the walk
and `f (next d) = d` exactly for first passages, then `f * formPerm c` moves exactly the
non-first passages. -/
theorem extremalJordanPickCountParity_support_eq (K : PocketFaceSet D eps X lo hi)
    (f : Equiv.Perm X.toCombMap.Dart) (hf : ∀ d, d ∉ K.boundary.cycle → f d = d)
    (hfirst : ∀ (d : X.toCombMap.Dart) (hd : d ∈ K.boundary.cycle),
      f (K.boundary.cycle.next d hd) = d ↔ ¬P10ChordLift.NonFirstTurn K d hd) :
    (f * K.boundary.cycle.formPerm).support = extremalJordanPickCountParity_nonFirst K := by
  ext d
  rw [Equiv.Perm.mem_support, Equiv.Perm.mul_apply, extremalJordanPickCountParity_mem_nonFirst]
  by_cases hd : d ∈ K.boundary.cycle
  · rw [List.formPerm_apply_mem_eq_next K.boundary.cycle_nodup d hd, ne_eq, hfirst d hd,
      not_not]
    constructor
    · intro h
      exact ⟨hd, h⟩
    · rintro ⟨_, h⟩
      exact h
  · rw [List.formPerm_apply_of_notMem hd, hf d hd]
    constructor
    · intro h
      exact absurd rfl h
    · rintro ⟨hd', -⟩
      exact absurd hd' hd

/-- **The per-pocket reduction.**  Let `f` fix the darts off the walk, with `f (next d) = d`
exactly for first passages.  If `#O` has the parity of the orbit count of `f` on the walk, then
the parity clause holds. -/
theorem extremalJordanPickCountParity_of_perm (K : PocketFaceSet D eps X lo hi)
    (h3 : ExtremalJordanPickEulerThreeAtVertex K)
    (f : Equiv.Perm X.toCombMap.Dart) (hf : ∀ d, d ∉ K.boundary.cycle → f d = d)
    (hfirst : ∀ (d : X.toCombMap.Dart) (hd : d ∈ K.boundary.cycle),
      f (K.boundary.cycle.next d hd) = d ↔ ¬P10ChordLift.NonFirstTurn K d hd)
    (hO : (extremalJordanPickCount_outside K).card % 2 =
      (K.boundary.cycle.length - f.support.card + f.cycleType.card) % 2) :
    ExtremalJordanPickCountParity K := by
  unfold ExtremalJordanPickCountParity
  intro hex hO2
  have h3' : (f * K.boundary.cycle.formPerm).support.card = 3 := by
    rw [extremalJordanPickCountParity_support_eq K f hf hfirst]
    exact extremalJordanPickCountParity_card_nonFirst K h3 hex
  have hodd := extremalJordanPickCountParity_perm_odd K.boundary.cycle K.boundary.cycle_nodup
    f hf h3'
  omega

end ParityPocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_mod_two_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_perm_odd
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_nonFirst
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_mem_nonFirst
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_card_nonFirst
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_support_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanPickCountParity_of_perm
