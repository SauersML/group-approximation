import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Predicate
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoublingFirstTurns
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterSpur
import GroupApproximation.Meta.AxiomGuard

/-!
# Chord lift: refinements of the rotation

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  An edge doubling inserts new darts into the
rotation at a vertex and changes nothing else near the old darts.  This module isolates the
map-level property that carries the turn data of an outer pinch pocket across such a surgery.

## The property

A **rotation refinement** `R : RotationRefinement M M'` is an injective dart map `e = R.map` with
`alpha' ∘ e = e ∘ alpha`, such that every rotation step lifts past new darts only: for every dart
`z` there is `m > 0` with `σ'^m (e z) = e (σ z)` and `σ'^t (e z) ∉ range e` for `0 < t < m`.

## Consequences

* `lift_pow`: `k` old steps lift to `K` new steps, `K > 0` iff `k > 0`, landing on `e (σ^k x)`; an
  image dart met strictly before `K` is `e (σ^t x)` with `0 < t < k`.  By induction on `k`: append
  the lift of the last step, whose intermediate darts are new.
* `project_pow`: `σ'^K (e x) = e y` gives `k ≤ K`, `K > 0 → k > 0`, `σ^k x = y`, and every
  intermediate `σ^t x`, `0 < t < k`, is met at some `0 < b < K`.  By strong induction on `K`: the
  lift `m` of the first step satisfies `m ≤ K`, since otherwise `σ'^K (e x)` is new; recurse at
  `σ x` with `K - m`.
* `rotationBetween_map_iff`: `RotationBetween M' (e x) (e y) (e z) ↔ RotationBetween M x y z`.  A
  witness projects; the intermediate darts met are images of old intermediates, so `e y` is met iff
  `y` is.  Conversely a witness lifts; the darts met are new or images of old intermediates.
* `sameCycle_map_iff`: finite orbits, `SameCycle.exists_nat_pow_eq`, then lift or project.
* `walkKeep_map_iff`, `not_walkKeep_map_of_new`: on a walk `c.map e`, an image `e z` is an edge dart
  iff `z` is one of `c` (because `alpha' (e z) = e (alpha z)`), and a new dart is never one, since
  `alpha'` of a new dart is new.
* `firstTurn_of_map`: a first turn along `c.map e` between images projects to a first turn along
  `c`: the rotation from `alpha' (e x) = e (alpha x)` projects, and every old intermediate is met in
  between, where no edge dart of `c.map e` lies.
* `refl`, `comp`: the identity refines, and refinements compose; the lift of the old step's lift meets
  only images of new darts of the first refinement, or new darts of the second, before its end.
* `edgeInsertion`: `EdgeInsertion.embed` refines `EdgeInsertion.toCombMap M a b` for `a ≠ b`
  (`EdgeInsertion.exists_sigma_step_lift`); this covers `FaceEdgeDoubling.map` and hence the outer
  spur thickening, whose maps are split maps at two distinct corners.
* `next_map_of_eq`, `sigma_ne_alpha_of_not_firstTurn`: successors in an image list, and a non-first
  turn is not the one-step turn.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift

universe v v' v''

open Equiv SimpleClosedWalkSides
open scoped Classical

/-- **A rotation refinement**: an injective dart map commuting with the edge reversal, along which
every rotation step lifts past new darts only. -/
structure RotationRefinement (M : CombMap.{v}) (M' : CombMap.{v'}) where
  /-- The dart map. -/
  map : M.Dart → M'.Dart
  injective : Function.Injective map
  alpha_map : ∀ d, M'.alpha (map d) = map (M.alpha d)
  step : ∀ z, ∃ m : ℕ, 0 < m ∧ (M'.sigma ^ m) (map z) = map (M.sigma z) ∧
    ∀ t, 0 < t → t < m → ∀ w, (M'.sigma ^ t) (map z) ≠ map w

namespace RotationRefinement

variable {M : CombMap.{v}} {M' : CombMap.{v'}} {M'' : CombMap.{v''}}

/-- **Old rotation steps lift.** -/
theorem lift_pow (R : RotationRefinement M M') (x : M.Dart) (k : ℕ) :
    ∃ K : ℕ, (0 < k → 0 < K) ∧ (0 < K → 0 < k) ∧
      (M'.sigma ^ K) (R.map x) = R.map ((M.sigma ^ k) x) ∧
      ∀ b, 0 < b → b < K → ∀ w, (M'.sigma ^ b) (R.map x) = R.map w →
        ∃ t, 0 < t ∧ t < k ∧ (M.sigma ^ t) x = w := by
  induction k with
  | zero =>
    refine ⟨0, fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h (Nat.lt_irrefl 0), ?_,
      fun b hb hbK => absurd (Nat.lt_trans hb hbK) (Nat.lt_irrefl 0)⟩
    simp only [pow_zero, Perm.one_apply]
  | succ k ih =>
    obtain ⟨K, -, hKk, hK, hKmid⟩ := ih
    obtain ⟨m, hm, hmz, hmmid⟩ := R.step ((M.sigma ^ k) x)
    refine ⟨m + K, fun _ => by omega, fun _ => Nat.succ_pos k, ?_, ?_⟩
    · rw [pow_add M'.sigma m K, Perm.mul_apply, hK, hmz, pow_succ' M.sigma k, Perm.mul_apply]
    · intro b hb hbK w hw
      rcases Nat.lt_or_ge b K with hlt | hge
      · obtain ⟨t, ht, htk, htw⟩ := hKmid b hb hlt w hw
        exact ⟨t, ht, Nat.lt_succ_of_lt htk, htw⟩
      · rcases Nat.eq_or_lt_of_le hge with heq | hgt
        · rw [← heq, hK] at hw
          exact ⟨k, hKk (by rw [heq]; exact hb), Nat.lt_succ_self k, R.injective hw⟩
        · obtain ⟨s, rfl⟩ : ∃ s, b = s + K := ⟨b - K, by omega⟩
          rw [pow_add M'.sigma s K, Perm.mul_apply, hK] at hw
          exact absurd hw (hmmid s (by omega) (by omega) w)

/-- **New rotation steps between images project.** -/
theorem project_pow (R : RotationRefinement M M') (K : ℕ) :
    ∀ x y : M.Dart, (M'.sigma ^ K) (R.map x) = R.map y →
      ∃ k, k ≤ K ∧ (0 < K → 0 < k) ∧ (M.sigma ^ k) x = y ∧
        ∀ t, 0 < t → t < k → ∃ b, 0 < b ∧ b < K ∧
          (M'.sigma ^ b) (R.map x) = R.map ((M.sigma ^ t) x) := by
  refine Nat.strong_induction_on K ?_
  intro K ih x y hK
  rcases Nat.eq_zero_or_pos K with h0 | hpos
  · subst h0
    simp only [pow_zero, Perm.one_apply] at hK
    refine ⟨0, le_rfl, fun h => absurd h (Nat.lt_irrefl 0), ?_,
      fun t ht htk => absurd (Nat.lt_trans ht htk) (Nat.lt_irrefl 0)⟩
    simp only [pow_zero, Perm.one_apply]
    exact R.injective hK
  · obtain ⟨m, hm, hmx, hmmid⟩ := R.step x
    have hmK : m ≤ K := by
      by_contra hlt
      exact hmmid K hpos (by omega) y hK
    have hrest : (M'.sigma ^ (K - m)) (R.map (M.sigma x)) = R.map y := by
      have h := hK
      rw [← Nat.sub_add_cancel hmK, pow_add M'.sigma (K - m) m, Perm.mul_apply, hmx] at h
      exact h
    obtain ⟨k, hkK, -, hk, hkmid⟩ := ih (K - m) (by omega) (M.sigma x) y hrest
    refine ⟨k + 1, by omega, fun _ => Nat.succ_pos k, ?_, ?_⟩
    · rw [pow_succ M.sigma k, Perm.mul_apply]
      exact hk
    · intro t ht htk
      rcases Nat.lt_or_ge t 2 with ht2 | ht2
      · obtain rfl : t = 1 := by omega
        exact ⟨m, hm, by omega, by rw [pow_one]; exact hmx⟩
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        obtain ⟨b, hb, hbK, hbs⟩ := hkmid s (by omega) (by omega)
        refine ⟨b + m, by omega, by omega, ?_⟩
        rw [pow_add M'.sigma b m, Perm.mul_apply, hmx, hbs, pow_succ M.sigma s, Perm.mul_apply]

/-- **Rotation sectors between images.** -/
theorem rotationBetween_map_iff (R : RotationRefinement M M') {x y z : M.Dart} :
    RotationBetween M' (R.map x) (R.map y) (R.map z) ↔ RotationBetween M x y z := by
  constructor
  · rintro ⟨A, hA, hAz, hAy⟩
    obtain ⟨k, -, hkpos, hk, hkmid⟩ := R.project_pow A x z hAz
    refine ⟨k, hkpos hA, hk, fun b hb hbk hby => ?_⟩
    rcases Nat.lt_or_ge b k with hlt | hge
    · obtain ⟨c, hc, hcA, hcb⟩ := hkmid b hb hlt
      exact hAy c hc (Nat.le_of_lt hcA) (by rw [hcb, hby])
    · rw [Nat.le_antisymm hbk hge, hk] at hby
      exact hAy A hA le_rfl (by rw [hAz, hby])
  · rintro ⟨a, ha, haz, hay⟩
    obtain ⟨A, hApos, -, hA, hAmid⟩ := R.lift_pow x a
    refine ⟨A, hApos ha, by rw [hA, haz], fun b hb hbA hby => ?_⟩
    rcases Nat.lt_or_ge b A with hlt | hge
    · obtain ⟨t, ht, hta, hty⟩ := hAmid b hb hlt y hby
      exact hay t ht (Nat.le_of_lt hta) hty
    · rw [Nat.le_antisymm hbA hge, hA, haz] at hby
      exact hay a ha le_rfl (by rw [haz]; exact R.injective hby)

/-- **Orbits between images.** -/
theorem sameCycle_map_iff (R : RotationRefinement M M') {x y : M.Dart} :
    M'.sigma.SameCycle (R.map x) (R.map y) ↔ M.sigma.SameCycle x y := by
  constructor
  · intro h
    obtain ⟨K, hK⟩ := h.exists_nat_pow_eq
    obtain ⟨k, -, -, hk, -⟩ := R.project_pow K x y hK
    exact ⟨(k : ℤ), by rw [zpow_natCast]; exact hk⟩
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    obtain ⟨K, -, -, hK, -⟩ := R.lift_pow x k
    exact ⟨(K : ℤ), by rw [zpow_natCast, hK, hk]⟩

/-- Membership of an image in an image list. -/
theorem mem_map_iff (R : RotationRefinement M M') {c : List M.Dart} {z : M.Dart} :
    R.map z ∈ c.map R.map ↔ z ∈ c := by
  constructor
  · intro h
    obtain ⟨w, hw, hwz⟩ := List.mem_map.mp h
    rw [← R.injective hwz]
    exact hw
  · intro h
    exact List.mem_map.mpr ⟨z, h, rfl⟩

/-- **Edge darts of an image walk, at images.** -/
theorem walkKeep_map_iff (R : RotationRefinement M M') (c : List M.Dart) (z : M.Dart) :
    walkKeep M' (c.map R.map) (R.map z) ↔ walkKeep M c z := by
  show (R.map z ∈ c.map R.map ∨ M'.alpha (R.map z) ∈ c.map R.map) ↔ (z ∈ c ∨ M.alpha z ∈ c)
  rw [R.alpha_map, R.mem_map_iff, R.mem_map_iff]

/-- **A new dart is off the edges of an image walk.** -/
theorem not_walkKeep_map_of_new (R : RotationRefinement M M') (c : List M.Dart) {n : M'.Dart}
    (hn : ∀ w, n ≠ R.map w) : ¬ walkKeep M' (c.map R.map) n := by
  rintro (h | h)
  · obtain ⟨w, -, hw⟩ := List.mem_map.mp h
    exact hn w hw.symm
  · obtain ⟨w, -, hw⟩ := List.mem_map.mp h
    refine hn (M.alpha w) ?_
    rw [← R.alpha_map, hw, M'.alpha_involutive n]

/-- **First turns between images project.** -/
theorem firstTurn_of_map (R : RotationRefinement M M') {c : List M.Dart} {x y : M.Dart}
    (h : FirstTurn M' (c.map R.map) (R.map x) (R.map y)) : FirstTurn M c x y := by
  obtain ⟨K, hK, hKy, hKmid⟩ := h
  rw [R.alpha_map] at hKy hKmid
  obtain ⟨k, -, hkpos, hk, hkmid⟩ := R.project_pow K (M.alpha x) y hKy
  refine ⟨k, hkpos hK, hk, fun t ht htk hkeep => ?_⟩
  obtain ⟨b, hb, hbK, hbt⟩ := hkmid t ht htk
  refine hKmid b hb hbK ?_
  rw [hbt]
  exact (R.walkKeep_map_iff c _).mpr hkeep

/-- **The identity refines the rotation.** -/
def refl (M : CombMap.{v}) : RotationRefinement M M where
  map d := d
  injective _ _ h := h
  alpha_map _ := rfl
  step z := ⟨1, Nat.one_pos, by rw [pow_one], fun _ ht ht1 => absurd ht1 (by omega)⟩

/-- **Refinements compose.** -/
def comp (R₁ : RotationRefinement M M') (R₂ : RotationRefinement M' M'') :
    RotationRefinement M M'' where
  map d := R₂.map (R₁.map d)
  injective := R₂.injective.comp R₁.injective
  alpha_map d := by rw [R₂.alpha_map, R₁.alpha_map]
  step z := by
    obtain ⟨m, hm, hmz, hmmid⟩ := R₁.step z
    obtain ⟨K, hKpos, -, hK, hKmid⟩ := R₂.lift_pow (R₁.map z) m
    refine ⟨K, hKpos hm, ?_, fun t ht htK w hw => ?_⟩
    · show (M''.sigma ^ K) (R₂.map (R₁.map z)) = R₂.map (R₁.map (M.sigma z))
      rw [hK, hmz]
    obtain ⟨s, hs, hsm, hsw⟩ := hKmid t ht htK (R₁.map w) hw
    exact hmmid s hs hsm w hsw

/-- **Edge insertion at two distinct corners refines the rotation.** -/
noncomputable def edgeInsertion {a b : M.Dart} (hab : a ≠ b) :
    RotationRefinement M (EdgeInsertion.toCombMap M a b) where
  map := EdgeInsertion.embed M
  injective d e h := Option.some.inj (Option.some.inj h)
  alpha_map _ := rfl
  step z := by
    obtain ⟨m, hm, hmz, hmmid⟩ := EdgeInsertion.exists_sigma_step_lift hab z
    refine ⟨m, hm, hmz, fun t ht htm w hw => ?_⟩
    rcases hmmid t ht htm with h | h
    · rw [h] at hw
      exact Option.noConfusion hw
    · rw [h] at hw
      exact Option.noConfusion (Option.some.inj hw)

end RotationRefinement

/-- Successors in an image list, through an equation of lists. -/
theorem next_map_of_eq {α β : Type*} {f : α → β} (hf : Function.Injective f) {l : List α}
    {l' : List β} (hl' : l' = l.map f) (hl : l.Nodup) {a : α} (ha : a ∈ l) (hb : f a ∈ l') :
    l'.next (f a) hb = f (l.next a ha) := by
  subst hl'
  exact OuterPinchCornerFix.next_map_of_injective hf hl ha hb

/-- A non-first turn is not the one-step turn: `σ e₀ ≠ α d₀`. -/
theorem sigma_ne_alpha_of_not_firstTurn {M : CombMap.{v}} {c : List M.Dart} {d₀ e₀ : M.Dart}
    (hnot : ¬ FirstTurn M c (M.alpha e₀) (M.alpha d₀)) : M.sigma e₀ ≠ M.alpha d₀ := by
  intro h
  refine hnot ⟨1, Nat.one_pos, ?_, fun t ht ht1 => absurd ht1 (by omega)⟩
  rw [pow_one, M.alpha_involutive e₀]
  exact h

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.RotationRefinement.lift_pow
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.RotationRefinement.project_pow
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.RotationRefinement.rotationBetween_map_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.RotationRefinement.sameCycle_map_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.RotationRefinement.mem_map_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.RotationRefinement.walkKeep_map_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.RotationRefinement.not_walkKeep_map_of_new
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.RotationRefinement.firstTurn_of_map
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.RotationRefinement.refl
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.RotationRefinement.comp
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.RotationRefinement.edgeInsertion
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.next_map_of_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.sigma_ne_alpha_of_not_firstTurn
