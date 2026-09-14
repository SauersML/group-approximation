import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoublingFirstTurns
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEulerNoninterleaving
import GroupApproximation.Meta.AxiomGuard

/-!
# The data of an outer pinch across one edge insertion

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  The pinch step at an outer pinch splits a vertex at a chord `d₀ → e₀` of the
boundary cycle, after fixing the corners of the split darts by inserting edges (a doubling of an edge,
or the thickening of an outer spur).  Each fix is an edge insertion `EdgeInsertion.toCombMap M a b` at
two distinct corners, and the chord data read on the old rotation carry over to the new one.

One old rotation step is one or two new steps, past new darts only
(`EdgeInsertion.exists_sigma_step_lift`, `Estimating/OsinPocketEdgeDoublingFirstTurns.lean`).  Choosing
those counts along the rotation from a dart `x` gives a strictly increasing count `liftCount x` with
`σ'^(liftCount x k) (embed x) = embed (σ^k x)`, and every new power from `embed x` lands on such an image
or on a new dart.  So runs of the rotation, the first return to a dart, and the sector relation
`RotationBetween` (`NoncrossingClosedWalkEulerNoninterleaving.lean`) transport.

* `EdgeInsertion.liftCount`, `sigma_pow_liftCount`, `liftCount_strictMono`: the count of new steps.
* `EdgeInsertion.sigma_pow_embed_cases`, `exists_liftCount_of_sigma_pow_embed`: every new power from an
  old dart is an image at a lifted count, or a new dart.
* `EdgeInsertion.minRun_embed`: a run to its first hit of a dart lifts.
* `EdgeInsertion.nonKeepRun_embed`, `nonKeepRunStrict_embed`: runs past darts off the edges of a walk
  lift, over the image walk.
* `EdgeInsertion.rotationBetween_embed_iff`: the sector relation on old darts is unchanged.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv SimpleClosedWalkSides

universe u

namespace EdgeInsertion

variable {M : CombMap.{u}} {a b : M.Dart} (hab : a ≠ b)

/-- The number of new rotation steps realizing one old step from `z`. -/
noncomputable def stepLen (z : M.Dart) : ℕ :=
  Classical.choose (exists_sigma_step_lift hab z)

theorem stepLen_pos (z : M.Dart) : 0 < stepLen hab z :=
  (Classical.choose_spec (exists_sigma_step_lift hab z)).1

theorem sigma_pow_stepLen (z : M.Dart) :
    ((toCombMap M a b).sigma ^ stepLen hab z) (embed M z) = embed M (M.sigma z) :=
  (Classical.choose_spec (exists_sigma_step_lift hab z)).2.1

theorem sigma_pow_new_of_lt_stepLen (z : M.Dart) {t : ℕ} (h0 : 0 < t) (ht : t < stepLen hab z) :
    ((toCombMap M a b).sigma ^ t) (embed M z) = none ∨
      ((toCombMap M a b).sigma ^ t) (embed M z) = some none :=
  (Classical.choose_spec (exists_sigma_step_lift hab z)).2.2 t h0 ht

/-- **The number of new rotation steps realizing `k` old steps from `x`.** -/
noncomputable def liftCount (x : M.Dart) : ℕ → ℕ
  | 0 => 0
  | k + 1 => liftCount x k + stepLen hab ((M.sigma ^ k) x)

theorem liftCount_zero (x : M.Dart) : liftCount hab x 0 = 0 :=
  rfl

theorem liftCount_succ (x : M.Dart) (k : ℕ) :
    liftCount hab x (k + 1) = liftCount hab x k + stepLen hab ((M.sigma ^ k) x) :=
  rfl

theorem liftCount_strictMono (x : M.Dart) : StrictMono (liftCount hab x) :=
  strictMono_nat_of_lt_succ fun k => by
    rw [liftCount_succ]
    have := stepLen_pos hab ((M.sigma ^ k) x)
    omega

theorem liftCount_pos (x : M.Dart) {k : ℕ} (hk : 0 < k) : 0 < liftCount hab x k := by
  have := liftCount_strictMono hab x hk
  rwa [liftCount_zero] at this

theorem pos_of_liftCount_pos (x : M.Dart) {k : ℕ} (h : 0 < liftCount hab x k) : 0 < k :=
  Nat.pos_of_ne_zero fun hk => by
    rw [hk, liftCount_zero] at h
    exact lt_irrefl 0 h

theorem le_liftCount (x : M.Dart) (k : ℕ) : k ≤ liftCount hab x k :=
  (liftCount_strictMono hab x).id_le k

/-- **The lifted count realizes the old run.** -/
theorem sigma_pow_liftCount (x : M.Dart) :
    ∀ k, ((toCombMap M a b).sigma ^ liftCount hab x k) (embed M x) = embed M ((M.sigma ^ k) x)
  | 0 => by
    rw [liftCount_zero, pow_zero, pow_zero, Perm.one_apply, Perm.one_apply]
  | k + 1 => by
    rw [liftCount_succ, Nat.add_comm (liftCount hab x k), pow_add, Perm.mul_apply,
      sigma_pow_liftCount x k, sigma_pow_stepLen, pow_succ', Perm.mul_apply]

/-- **Every new power from an old dart is an image at a lifted count, or a new dart.** -/
theorem sigma_pow_embed_cases (x : M.Dart) (t : ℕ) :
    (∃ k, liftCount hab x k = t ∧
        ((toCombMap M a b).sigma ^ t) (embed M x) = embed M ((M.sigma ^ k) x)) ∨
      ((toCombMap M a b).sigma ^ t) (embed M x) = none ∨
      ((toCombMap M a b).sigma ^ t) (embed M x) = some none := by
  classical
  have hex : ∃ k, t < liftCount hab x (k + 1) :=
    ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) (le_liftCount hab x (t + 1))⟩
  obtain ⟨k, hlt, hmin⟩ : ∃ k, t < liftCount hab x (k + 1) ∧
      ∀ j, j < k → ¬ t < liftCount hab x (j + 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hle : liftCount hab x k ≤ t := by
    rcases k with _ | k'
    · rw [liftCount_zero]
      exact Nat.zero_le t
    · have h := hmin k' (Nat.lt_succ_self k')
      omega
  by_cases heq : liftCount hab x k = t
  · left
    refine ⟨k, heq, ?_⟩
    rw [← heq]
    exact sigma_pow_liftCount hab x k
  · right
    have hs0 : 0 < t - liftCount hab x k := by omega
    have hs : t - liftCount hab x k < stepLen hab ((M.sigma ^ k) x) := by
      rw [liftCount_succ] at hlt
      omega
    have ht : t = (t - liftCount hab x k) + liftCount hab x k := by omega
    rw [ht, pow_add, Perm.mul_apply, sigma_pow_liftCount hab x k]
    exact sigma_pow_new_of_lt_stepLen hab _ hs0 hs

/-- **A new power from an old dart onto an old dart is a lifted count.** -/
theorem exists_liftCount_of_sigma_pow_embed (x z : M.Dart) {t : ℕ}
    (h : ((toCombMap M a b).sigma ^ t) (embed M x) = embed M z) :
    ∃ k, liftCount hab x k = t ∧ (M.sigma ^ k) x = z := by
  rcases sigma_pow_embed_cases hab x t with ⟨k, hk, hk'⟩ | hnone | hsome
  · exact ⟨k, hk, embed_injective M (hk'.symm.trans h)⟩
  · rw [hnone] at h
    exact absurd h (by simp [embed])
  · rw [hsome] at h
    have h' : (some none : Option (Option M.Dart)) = some (some z) := h
    cases h'

/-- **A run to the first hit of a dart lifts.** -/
theorem minRun_embed (x y : M.Dart) {k : ℕ} (hk : (M.sigma ^ k) x = y)
    (hmin : ∀ t, 0 < t → t < k → (M.sigma ^ t) x ≠ y) :
    ((toCombMap M a b).sigma ^ liftCount hab x k) (embed M x) = embed M y ∧
      ∀ t', 0 < t' → t' < liftCount hab x k →
        ((toCombMap M a b).sigma ^ t') (embed M x) ≠ embed M y := by
  refine ⟨by rw [sigma_pow_liftCount, hk], fun t' ht'0 ht'k ht'y => ?_⟩
  obtain ⟨j, hj, hjy⟩ := exists_liftCount_of_sigma_pow_embed hab x y ht'y
  have hj0 : 0 < j := pos_of_liftCount_pos hab x (by rw [hj]; exact ht'0)
  exact hmin j hj0 ((liftCount_strictMono hab x).lt_iff_lt.mp (by rw [hj]; exact ht'k)) hjy

/-- **A run past darts off the edges of a walk lifts**, over the image walk, with its end. -/
theorem nonKeepRun_embed (c : List M.Dart) (x z : M.Dart) {m : ℕ} (hm : (M.sigma ^ m) x = z)
    (hkeep : ∀ t, 0 < t → t ≤ m → ¬ walkKeep M c ((M.sigma ^ t) x)) :
    ((toCombMap M a b).sigma ^ liftCount hab x m) (embed M x) = embed M z ∧
      ∀ t', 0 < t' → t' ≤ liftCount hab x m →
        ¬ walkKeep (toCombMap M a b) (c.map (embed M))
          (((toCombMap M a b).sigma ^ t') (embed M x)) := by
  refine ⟨by rw [sigma_pow_liftCount, hm], fun t' ht'0 ht'm => ?_⟩
  rcases sigma_pow_embed_cases hab x t' with ⟨j, hj, hjx⟩ | hnone | hsome
  · rw [hjx, walkKeep_map_embed_iff]
    exact hkeep j (pos_of_liftCount_pos hab x (by rw [hj]; exact ht'0))
      ((liftCount_strictMono hab x).le_iff_le.mp (by rw [hj]; exact ht'm))
  · rw [hnone]
    exact not_walkKeep_map_embed_none a b c
  · rw [hsome]
    exact not_walkKeep_map_embed_some_none a b c

/-- **A run past darts off the edges of a walk lifts**, over the image walk, before its end. -/
theorem nonKeepRunStrict_embed (c : List M.Dart) (y z : M.Dart) {q : ℕ} (hq : (M.sigma ^ q) y = z)
    (hkeep : ∀ t, 0 < t → t < q → ¬ walkKeep M c ((M.sigma ^ t) y)) :
    ((toCombMap M a b).sigma ^ liftCount hab y q) (embed M y) = embed M z ∧
      ∀ t', 0 < t' → t' < liftCount hab y q →
        ¬ walkKeep (toCombMap M a b) (c.map (embed M))
          (((toCombMap M a b).sigma ^ t') (embed M y)) := by
  refine ⟨by rw [sigma_pow_liftCount, hq], fun t' ht'0 ht'q => ?_⟩
  rcases sigma_pow_embed_cases hab y t' with ⟨j, hj, hjy⟩ | hnone | hsome
  · rw [hjy, walkKeep_map_embed_iff]
    exact hkeep j (pos_of_liftCount_pos hab y (by rw [hj]; exact ht'0))
      ((liftCount_strictMono hab y).lt_iff_lt.mp (by rw [hj]; exact ht'q))
  · rw [hnone]
    exact not_walkKeep_map_embed_none a b c
  · rw [hsome]
    exact not_walkKeep_map_embed_some_none a b c

include hab in
/-- **The sector relation on old darts is unchanged by the insertion.** -/
theorem rotationBetween_embed_iff (x y z : M.Dart) :
    RotationBetween (toCombMap M a b) (embed M x) (embed M y) (embed M z) ↔
      RotationBetween M x y z := by
  constructor
  · rintro ⟨n', hn'0, hn'z, hno'⟩
    obtain ⟨k, hk, hkz⟩ := exists_liftCount_of_sigma_pow_embed hab x z hn'z
    refine ⟨k, pos_of_liftCount_pos hab x (by rw [hk]; exact hn'0), hkz, fun j hj0 hjk hjy => ?_⟩
    refine hno' (liftCount hab x j) (liftCount_pos hab x hj0) ?_ ?_
    · rw [← hk]
      exact (liftCount_strictMono hab x).monotone hjk
    · rw [sigma_pow_liftCount, hjy]
  · rintro ⟨k, hk0, hkz, hno⟩
    refine ⟨liftCount hab x k, liftCount_pos hab x hk0, by rw [sigma_pow_liftCount, hkz],
      fun n' hn'0 hn'k hn'y => ?_⟩
    obtain ⟨j, hj, hjy⟩ := exists_liftCount_of_sigma_pow_embed hab x y hn'y
    exact hno j (pos_of_liftCount_pos hab x (by rw [hj]; exact hn'0))
      ((liftCount_strictMono hab x).le_iff_le.mp (by rw [hj]; exact hn'k)) hjy

end EdgeInsertion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.liftCount
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.sigma_pow_liftCount
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.liftCount_strictMono
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.sigma_pow_embed_cases
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.exists_liftCount_of_sigma_pow_embed
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.minRun_embed
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.nonKeepRun_embed
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.nonKeepRunStrict_embed
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.rotationBetween_embed_iff
