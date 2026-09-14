import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoublingFirstTurns
import GroupApproximation.Meta.AxiomGuard

/-!
# First turns across the doubling of a bridge dart

`EnclosedBridgeDoublingSuccStatement` (`ClosedWalkEnclosedSubdiagramPieces`) thickens every bridge
edge of an outside walk into a digon.  One thickening is an edge insertion
`EdgeInsertion.toCombMap M a b` at the corners `a = d₀`, a dart of the walk whose reverse is on the
walk too, and `b = σ (α d₀)`.  The new dart `some none` takes the place of `d₀` on the walk; the
new dart `none` is its reverse.  So the image walk is `w.map (image M d₀)`, with `image M d₀ d₀ =
some none` and `image M d₀ z = embed z` otherwise.

The rotation of the insertion places `some none` right before `embed a` and `none` right after
`embed (σ⁻¹ b) = embed (α d₀)`.  Both lie on edges of the image walk, as do exactly the images of
the old darts on edges of the walk.  A first turn from the image of an old dart meets no new dart
before its end: `some none` only where the old turn ends at `a`, and `none` only after `α d₀`, which
is on the walk.  So the successor form of the turning condition carries over.

* `sigma_eq_none_iff`, `sigma_eq_embed_iff_some_none`: where the new darts sit in the rotation.
* `firstKept_lift`: a first run to a kept dart lifts, ending at `some none` when it ended at `a`.
* `first_kept_unique`: two first runs to kept darts from one start have the same length.
* `exists_first_kept_of_alpha_mem`: from the reverse of a walk dart a first run exists.
* `walkKeep_image_iff`: an old dart is on an edge of the image walk exactly when it is on an edge of
  the walk, for a bridge dart `d₀`.
* `turn_next_image`: the successor form of the image walk.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemmas 9.4 and 9.7); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u

open Equiv SimpleClosedWalkSides EdgeInsertion

namespace EnclosedBridgeDoubling

variable {M : CombMap.{u}}

/-- The dart map of a doubling at `d₀`: `d₀` goes to the new dart `some none`. -/
noncomputable def image (M : CombMap.{u}) (d₀ : M.Dart) (z : M.Dart) : EdgeInsertion.Dart M := by
  classical
  exact if z = d₀ then some none else embed M z

theorem image_self (d₀ : M.Dart) : image M d₀ d₀ = some none := by
  classical
  simp [image]

theorem image_of_ne {d₀ z : M.Dart} (hz : z ≠ d₀) : image M d₀ z = embed M z := by
  classical
  simp [image, hz]

theorem image_injective (d₀ : M.Dart) : Function.Injective (image M d₀) := by
  classical
  intro y z h
  by_cases hy : y = d₀
  · by_cases hz : z = d₀
    · exact hy.trans hz.symm
    · rw [hy, image_self, image_of_ne hz] at h
      cases h
  · by_cases hz : z = d₀
    · rw [hz, image_self, image_of_ne hy] at h
      cases h
    · rw [image_of_ne hy, image_of_ne hz] at h
      exact embed_injective M h

theorem image_ne_none (d₀ z : M.Dart) : image M d₀ z ≠ none := by
  classical
  unfold image
  split_ifs <;> simp [embed]

theorem image_eq_embed_iff {d₀ y z : M.Dart} : image M d₀ y = embed M z ↔ y = z ∧ y ≠ d₀ := by
  classical
  by_cases hy : y = d₀
  · rw [hy, image_self]
    exact ⟨fun h => (by cases h), fun h => absurd rfl h.2⟩
  · rw [image_of_ne hy]
    exact ⟨fun h => ⟨embed_injective M h, hy⟩, fun h => by rw [h.1]⟩

/-! ## The new darts in the rotation -/

/-- `none` follows exactly the image of `σ⁻¹ b`. -/
theorem sigma_eq_none_iff [DecidableEq M.Dart] {a b : M.Dart} (hab : a ≠ b)
    (y : (toCombMap M a b).Dart) :
    (toCombMap M a b).sigma y = none ↔ y = embed M (M.sigma.symm b) := by
  rcases y with _ | _ | z
  · rw [sigma_none_apply]
    simp [embed]
  · rw [GeodesicCollar.edgeInsertion_sigma_some_none hab]
    exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  · change (toCombMap M a b).sigma (embed M z) = none ↔ embed M z = embed M (M.sigma.symm b)
    rw [sigma_embed_apply hab, (embed_injective M).eq_iff]
    by_cases ha : M.sigma z = a
    · rw [if_pos ha]
      constructor
      · intro h
        cases h
      · intro hz
        have h2 : M.sigma z = b := by rw [hz, Equiv.apply_symm_apply]
        exact absurd (ha.symm.trans h2) hab
    · rw [if_neg ha]
      by_cases hb : M.sigma z = b
      · rw [if_pos hb]
        exact ⟨fun _ => by rw [← hb, Equiv.symm_apply_apply], fun _ => rfl⟩
      · rw [if_neg hb]
        constructor
        · intro h
          cases h
        · intro hz
          have h2 : M.sigma z = b := by rw [hz, Equiv.apply_symm_apply]
          exact absurd h2 hb

/-- The image of `a` follows exactly `some none`. -/
theorem sigma_eq_embed_iff_some_none [DecidableEq M.Dart] {a b : M.Dart} (hab : a ≠ b)
    (y : (toCombMap M a b).Dart) :
    (toCombMap M a b).sigma y = embed M a ↔ y = some none := by
  rcases y with _ | _ | z
  · rw [sigma_none_apply]
    exact ⟨fun h => absurd (embed_injective M h).symm hab, fun h => (by cases h)⟩
  · rw [GeodesicCollar.edgeInsertion_sigma_some_none hab]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · change (toCombMap M a b).sigma (embed M z) = embed M a ↔ embed M z = some none
    rw [sigma_embed_apply hab]
    by_cases ha : M.sigma z = a
    · rw [if_pos ha]
      exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
    · rw [if_neg ha]
      by_cases hb : M.sigma z = b
      · rw [if_pos hb]
        exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
      · rw [if_neg hb]
        exact ⟨fun h => absurd (embed_injective M h) ha, fun h => (by cases h)⟩

/-! ## Runs to the first kept dart -/

/-- **A first run to a kept dart lifts** across the insertion, when `a` and `σ⁻¹ b` are kept and the
run does not start at `σ⁻¹ b`.  The lifted run ends at `some none` if the old one ended at `a`, and
at the image of the old end otherwise, meeting no kept dart before. -/
theorem firstKept_lift [DecidableEq M.Dart] {a b : M.Dart} (hab : a ≠ b)
    {keep : M.Dart → Prop} {keep' : (toCombMap M a b).Dart → Prop}
    (hkeep : ∀ z, keep' (embed M z) ↔ keep z) (ha : keep a) (hb : keep (M.sigma.symm b))
    {x : M.Dart} (hx : x ≠ M.sigma.symm b) {m : ℕ} (hm : 0 < m)
    (hfirst : ∀ t, 0 < t → t < m → ¬ keep ((M.sigma ^ t) x)) :
    ∃ k', 0 < k' ∧
      ((toCombMap M a b).sigma ^ k') (embed M x) =
        (if (M.sigma ^ m) x = a then some none else embed M ((M.sigma ^ m) x)) ∧
      ∀ t', 0 < t' → t' < k' → ¬ keep' (((toCombMap M a b).sigma ^ t') (embed M x)) := by
  obtain ⟨k', hkk', -, heq, hmid⟩ := exists_sigma_pow_lift hab x m
  have hnone : ∀ t', 0 < t' → t' < k' →
      ((toCombMap M a b).sigma ^ t') (embed M x) ≠ none := by
    intro t' ht'0 ht'k hn
    obtain ⟨s, rfl⟩ : ∃ s, t' = s + 1 := ⟨t' - 1, by omega⟩
    rw [pow_succ', Perm.mul_apply, sigma_eq_none_iff hab] at hn
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · rw [pow_zero, Perm.one_apply] at hn
      exact hx (embed_injective M hn)
    · rcases hmid s hs (by omega) with ⟨t, ht0, htm, h⟩ | h | h
      · rw [hn] at h
        have hxt : M.sigma.symm b = (M.sigma ^ t) x := embed_injective M h
        exact hfirst t ht0 htm (by rw [← hxt]; exact hb)
      · rw [hn] at h
        cases h
      · rw [hn] at h
        cases h
  have hsome : ∀ t', 0 < t' → t' < k' →
      ((toCombMap M a b).sigma ^ t') (embed M x) = some none →
        t' + 1 = k' ∧ (M.sigma ^ m) x = a := by
    intro t' ht'0 ht'k hsn
    have hnext : ((toCombMap M a b).sigma ^ (t' + 1)) (embed M x) = embed M a := by
      rw [pow_succ', Perm.mul_apply, hsn, GeodesicCollar.edgeInsertion_sigma_some_none hab]
    by_cases hlt : t' + 1 < k'
    · exfalso
      rcases hmid (t' + 1) (by omega) hlt with ⟨t, ht0, htm, h⟩ | h | h
      · rw [hnext] at h
        have hat : a = (M.sigma ^ t) x := embed_injective M h
        exact hfirst t ht0 htm (by rw [← hat]; exact ha)
      · rw [hnext] at h
        cases h
      · rw [hnext] at h
        cases h
    · have hk : t' + 1 = k' := by omega
      refine ⟨hk, ?_⟩
      rw [hk, heq] at hnext
      exact embed_injective M hnext
  by_cases hma : (M.sigma ^ m) x = a
  · rw [if_pos hma]
    obtain ⟨s, rfl⟩ : ∃ s, k' = s + 1 := ⟨k' - 1, by omega⟩
    have hpre : ((toCombMap M a b).sigma ^ s) (embed M x) = some none := by
      have h := heq
      rw [pow_succ', Perm.mul_apply, hma] at h
      exact (sigma_eq_embed_iff_some_none hab _).mp h
    have hs0 : 0 < s := by
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · rw [pow_zero, Perm.one_apply] at hpre
        cases hpre
      · exact hs
    refine ⟨s, hs0, hpre, fun t' ht'0 ht's => ?_⟩
    rcases hmid t' ht'0 (by omega) with ⟨t, ht0, htm, h⟩ | h | h
    · rw [h, hkeep]
      exact hfirst t ht0 htm
    · exact absurd h (hnone t' ht'0 (by omega))
    · exact absurd (hsome t' ht'0 (by omega) h).1 (by omega)
  · rw [if_neg hma]
    refine ⟨k', by omega, heq, fun t' ht'0 ht'k => ?_⟩
    rcases hmid t' ht'0 ht'k with ⟨t, ht0, htm, h⟩ | h | h
    · rw [h, hkeep]
      exact hfirst t ht0 htm
    · exact absurd h (hnone t' ht'0 ht'k)
    · exact absurd (hsome t' ht'0 ht'k h).2 hma

/-- Two first runs to kept darts from one start have the same length. -/
theorem first_kept_unique {α : Type*} {p : Perm α} {keep : α → Prop} {s : α} {m k : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hkm : keep ((p ^ m) s))
    (hfm : ∀ t, 0 < t → t < m → ¬ keep ((p ^ t) s)) (hkk : keep ((p ^ k) s))
    (hfk : ∀ t, 0 < t → t < k → ¬ keep ((p ^ t) s)) : m = k := by
  rcases lt_trichotomy m k with h | h | h
  · exact absurd hkm (hfk m hm h)
  · exact h
  · exact absurd hkk (hfm k hk h)

/-- From the reverse of a walk dart, a first run to a dart on an edge of the walk exists. -/
theorem exists_first_kept_of_alpha_mem {w : List M.Dart} {x : M.Dart} (hx : x ∈ w) :
    ∃ m, 0 < m ∧ walkKeep M w ((M.sigma ^ m) (M.alpha x)) ∧
      ∀ k, 0 < k → k < m → ¬ walkKeep M w ((M.sigma ^ k) (M.alpha x)) := by
  classical
  have hex : ∃ m, 0 < m ∧ walkKeep M w ((M.sigma ^ m) (M.alpha x)) := by
    refine ⟨orderOf M.sigma, orderOf_pos _, ?_⟩
    rw [pow_orderOf_eq_one, Perm.one_apply]
    exact Or.inr (by rw [M.alpha_involutive x]; exact hx)
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hk hkm hkeep => ?_⟩
  exact Nat.find_min hex hkm ⟨hk, hkeep⟩

/-! ## The image walk -/

/-- **An old dart is on an edge of the image walk exactly when it is on an edge of the walk**, when
both `d₀` and its reverse are walk darts. -/
theorem walkKeep_image_iff {a b : M.Dart} {w : List M.Dart} (hd₀ : a ∈ w)
    (had₀ : M.alpha a ∈ w) (z : M.Dart) :
    walkKeep (toCombMap M a b) (w.map (image M a)) (embed M z) ↔ walkKeep M w z := by
  change embed M z ∈ w.map (image M a) ∨ embed M (M.alpha z) ∈ w.map (image M a) ↔
    z ∈ w ∨ M.alpha z ∈ w
  simp only [List.mem_map, image_eq_embed_iff]
  constructor
  · rintro (⟨y, hy, rfl, -⟩ | ⟨y, hy, rfl, -⟩)
    · exact Or.inl hy
    · exact Or.inr hy
  · rintro (hz | hz)
    · by_cases hza : z = a
      · subst hza
        refine Or.inr ⟨M.alpha z, had₀, rfl, fun h => M.alpha_fixedPointFree z h⟩
      · exact Or.inl ⟨z, hz, rfl, hza⟩
    · by_cases hza : M.alpha z = a
      · refine Or.inl ⟨z, ?_, rfl, fun h => ?_⟩
        · rw [← M.alpha_involutive z, hza]
          exact had₀
        · rw [h] at hza
          exact M.alpha_fixedPointFree a hza
      · exact Or.inr ⟨M.alpha z, hz, rfl, hza⟩

theorem walkKeep_image_none {a b : M.Dart} {w : List M.Dart} (hd₀ : a ∈ w) :
    walkKeep (toCombMap M a b) (w.map (image M a)) none :=
  Or.inr (List.mem_map.mpr ⟨a, hd₀, image_self a⟩)

theorem walkKeep_image_some_none {a b : M.Dart} {w : List M.Dart} (hd₀ : a ∈ w) :
    walkKeep (toCombMap M a b) (w.map (image M a)) (some none) :=
  Or.inl (List.mem_map.mpr ⟨a, hd₀, image_self a⟩)

theorem walkKeep_image_image {a b : M.Dart} {w : List M.Dart} {y : M.Dart} (hy : y ∈ w) :
    walkKeep (toCombMap M a b) (w.map (image M a)) (image M a y) :=
  Or.inl (List.mem_map.mpr ⟨y, hy, rfl⟩)

theorem alpha_image {a b : M.Dart} (z : M.Dart) (hz : z ≠ a) :
    (toCombMap M a b).alpha (image M a z) = embed M (M.alpha z) := by
  rw [image_of_ne hz]
  rfl

/-- **The successor form carries over to the image walk** of a doubling at a bridge dart `a`, with
`b = σ (α a)`. -/
theorem turn_next_image [DecidableEq M.Dart] {a b : M.Dart} (hab : a ≠ b)
    (hb : M.sigma (M.alpha a) = b) {w : List M.Dart} (hd₀ : a ∈ w) (had₀ : M.alpha a ∈ w)
    (hturn : ∀ (i : ℕ) (hi : i < w.length) (m : ℕ), 0 < m →
      walkKeep M w ((M.sigma ^ m) (M.alpha w[i])) →
      (∀ k, 0 < k → k < m → ¬ walkKeep M w ((M.sigma ^ k) (M.alpha w[i]))) →
      (M.sigma ^ m) (M.alpha w[i]) = w[(i + 1) % w.length]'
        (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)))
    (i : ℕ) (hi : i < (w.map (image M a)).length) (m' : ℕ) (hm' : 0 < m')
    (hkeep' : walkKeep (toCombMap M a b) (w.map (image M a))
      (((toCombMap M a b).sigma ^ m') ((toCombMap M a b).alpha (w.map (image M a))[i])))
    (hfirst' : ∀ k, 0 < k → k < m' → ¬ walkKeep (toCombMap M a b) (w.map (image M a))
      (((toCombMap M a b).sigma ^ k) ((toCombMap M a b).alpha (w.map (image M a))[i]))) :
    ((toCombMap M a b).sigma ^ m') ((toCombMap M a b).alpha (w.map (image M a))[i]) =
      (w.map (image M a))[(i + 1) % (w.map (image M a)).length]'
        (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) := by
  have hi0 : i < w.length := by simpa using hi
  have hlen : (w.map (image M a)).length = w.length := List.length_map _
  have hnext : (w.map (image M a))[(i + 1) % (w.map (image M a)).length]'
      (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) =
        image M a (w[(i + 1) % w.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi0))) := by
    simp [hlen]
  have hcur : (w.map (image M a))[i] = image M a w[i] := by simp
  rw [hnext]
  rw [hcur] at hkeep' hfirst' ⊢
  obtain ⟨m, hm, hkm, hfm⟩ := exists_first_kept_of_alpha_mem (List.getElem_mem hi0)
  have hold := hturn i hi0 m hm hkm hfm
  have hsymm : M.sigma.symm b = M.alpha a := by rw [← hb, Equiv.symm_apply_apply]
  have hkeepI := walkKeep_image_iff (b := b) hd₀ had₀
  have ha' : walkKeep M w a := Or.inl hd₀
  have hb' : walkKeep M w (M.sigma.symm b) := by rw [hsymm]; exact Or.inl had₀
  have hend : walkKeep (toCombMap M a b) (w.map (image M a))
      (image M a (w[(i + 1) % w.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi0)))) :=
    walkKeep_image_image (List.getElem_mem _)
  by_cases hxa : w[i] = a
  · -- the start is `none`
    have hstart : (toCombMap M a b).alpha (image M a w[i]) = none := by
      rw [hxa, image_self]
      rfl
    rw [hstart] at hkeep' hfirst' ⊢
    have hstep : (toCombMap M a b).sigma none = embed M b := sigma_none_apply a b
    rw [hxa] at hold hkm hfm
    rcases Nat.lt_or_ge 1 m with h1 | h1
    · -- `b` is off the walk; lift the rest of the run from `b`
      have hbnot : ¬ walkKeep M w b := by
        have := hfm 1 Nat.one_pos h1
        rwa [pow_one, hb] at this
      have hbne : b ≠ M.sigma.symm b := fun h => hbnot (h ▸ hb')
      have hfb : ∀ t, 0 < t → t < m - 1 → ¬ walkKeep M w ((M.sigma ^ t) b) := by
        intro t ht0 htm
        have := hfm (t + 1) (by omega) (by omega)
        rwa [pow_succ, Perm.mul_apply, hb] at this
      have hmb : (M.sigma ^ (m - 1)) b = (M.sigma ^ m) (M.alpha a) := by
        rw [← hb, ← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega)]
      obtain ⟨k', hk'0, hk'eq, hk'mid⟩ :=
        firstKept_lift hab hkeepI ha' hb' hbne (by omega : 0 < m - 1) hfb
      have hrun : ((toCombMap M a b).sigma ^ (k' + 1)) none =
          image M a (w[(i + 1) % w.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi0))) := by
        rw [pow_succ, Perm.mul_apply, hstep, hk'eq, hmb, hold]
        unfold image
        split_ifs <;> rfl
      have hfirstRun : ∀ t, 0 < t → t < k' + 1 →
          ¬ walkKeep (toCombMap M a b) (w.map (image M a)) (((toCombMap M a b).sigma ^ t) none) := by
        intro t ht0 htk
        rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt ht0) with h | h
        · rw [← h, pow_one, hstep, hkeepI]
          exact hbnot
        · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
          rw [pow_succ, Perm.mul_apply, hstep]
          exact hk'mid s (by omega) (by omega)
      have heqlen := first_kept_unique hm' (Nat.succ_pos k') hkeep' hfirst'
        (by rw [hrun]; exact hend) hfirstRun
      rw [heqlen, hrun]
    · -- `b` is the first kept dart
      obtain rfl : m = 1 := by omega
      rw [pow_one, hb] at hold
      have hbimg : image M a b = embed M b := image_of_ne (Ne.symm hab)
      have heqlen := first_kept_unique hm' Nat.one_pos hkeep' hfirst'
        (by rw [pow_one, hstep, ← hbimg, hold]; exact hend)
        (fun t ht0 ht1 => absurd ht1 (by omega))
      rw [heqlen, pow_one, hstep, ← hbimg, hold]
  · -- the start is the image of an old dart
    have hstart : (toCombMap M a b).alpha (image M a w[i]) = embed M (M.alpha w[i]) :=
      alpha_image _ hxa
    rw [hstart] at hkeep' hfirst' ⊢
    have hxne : M.alpha w[i] ≠ M.sigma.symm b := by
      rw [hsymm]
      intro h
      exact hxa (M.alpha.injective h)
    obtain ⟨k', hk'0, hk'eq, hk'mid⟩ := firstKept_lift hab hkeepI ha' hb' hxne hm hfm
    have hrun : ((toCombMap M a b).sigma ^ k') (embed M (M.alpha w[i])) =
        image M a (w[(i + 1) % w.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi0))) := by
      rw [hk'eq, hold]
      unfold image
      split_ifs <;> rfl
    have heqlen := first_kept_unique hm' hk'0 hkeep' hfirst' (by rw [hrun]; exact hend) hk'mid
    rw [heqlen, hrun]

end EnclosedBridgeDoubling

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.EnclosedBridgeDoubling

#audit_axioms sigma_eq_none_iff
#audit_axioms sigma_eq_embed_iff_some_none
#audit_axioms firstKept_lift
#audit_axioms exists_first_kept_of_alpha_mem
#audit_axioms walkKeep_image_iff
#audit_axioms turn_next_image
