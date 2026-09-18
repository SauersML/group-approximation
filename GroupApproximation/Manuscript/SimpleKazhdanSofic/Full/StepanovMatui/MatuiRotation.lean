import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiThinRoom
import GroupApproximation.Meta.AxiomGuard

/-!
# Rotating a thin tower: commutators with `T`

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–315 (Matui, Lemma 3.4 and Theorem 4.9).

Let `Y` wander up to `L` (`Wandering T Y L`) with `2M + 1 ≤ L`. The levels `T^j Y` for
`-M ≤ j ≤ M + 1` are pairwise disjoint. `thinRot` moves level `j` to level `j + 1` along `T` for
`j ≤ M`, sends the top level `M + 1` back to level `-M`, and fixes everything else. It is an element
of `[[T]]` supported in `thin T Y (M + 1)` that agrees with `T` on `thin T Y M`. This is the
Kakutani–Rokhlin rotation of Matui (Internat. J. Math. 2006, §4) and Grigorchuk–Medynets (2014, §3).

* `commutatorElement_toEquiv_mem`: if `6M + 8 ≤ L` and `r ∈ [[T]]` is supported in
  `thin T Y M`, then `⁅T, r⁆ = ⁅thinRot, r⁆ ∈ alternatingFullGroup T` by the room lemma
  `commutatorElement_mem_of_supportedIn_thin`.
-/

namespace GroupApproximation
namespace Full
namespace StepanovMatui
namespace Matui

open scoped commutatorElement

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {Y : Set X} {L M : ℕ}

theorem zpow_apply_zpow_apply_of_eq (T : X ≃ₜ X) (a b c : ℤ) (h : a + b = c) (x : X) :
    (T ^ a) ((T ^ b) x) = (T ^ c) x := by
  rw [zpow_apply_zpow_apply, h]

theorem homeo_zpow_zero_apply (T : X ≃ₜ X) (x : X) : (T ^ (0 : ℤ)) x = x := by
  rw [zpow_zero, Homeomorph.one_apply]

/-- Two points of `Y` on one orbit at distance `0 < |b - a| ≤ L` contradict wandering. -/
theorem Wandering.notMem (hY : Wandering T Y L) {a b : ℤ} (hab : a ≠ b) (h1 : b - a ≤ L)
    (h2 : a - b ≤ L) {x : X} (ha : (T ^ a) x ∈ Y) : (T ^ b) x ∉ Y := by
  intro hb
  refine hY (b - a) (by omega) (by omega) h1 _ ha ?_
  rw [zpow_apply_zpow_apply_of_eq T (b - a) a b (by ring) x]
  exact hb

open Classical in
/-- The rotation of the levels `-M, …, M + 1` of the tower over `Y`, as a function. -/
noncomputable def thinRotFun (T : X ≃ₜ X) (Y : Set X) (M : ℕ) (x : X) : X :=
  if x ∈ thin T Y M then (T ^ (1 : ℤ)) x
  else if (T ^ (-((M : ℤ) + 1))) x ∈ Y then (T ^ (-(2 * (M : ℤ) + 1))) x else x

open Classical in
/-- The inverse rotation, as a function. -/
noncomputable def thinRotInvFun (T : X ≃ₜ X) (Y : Set X) (M : ℕ) (x : X) : X :=
  if (T ^ (-1 : ℤ)) x ∈ thin T Y M then (T ^ (-1 : ℤ)) x
  else if (T ^ (M : ℤ)) x ∈ Y then (T ^ (2 * (M : ℤ) + 1)) x else x

open Classical in
/-- The cocycle of the rotation. -/
noncomputable def thinRotCocycle (T : X ≃ₜ X) (Y : Set X) (M : ℕ) (x : X) : ℤ :=
  if x ∈ thin T Y M then 1 else if (T ^ (-((M : ℤ) + 1))) x ∈ Y then -(2 * (M : ℤ) + 1) else 0

theorem thinRotFun_of_mem {x : X} (hx : x ∈ thin T Y M) :
    thinRotFun T Y M x = (T ^ (1 : ℤ)) x := by
  unfold thinRotFun
  rw [if_pos hx]

theorem thinRotFun_of_top {x : X} (hx : x ∉ thin T Y M) (hQ : (T ^ (-((M : ℤ) + 1))) x ∈ Y) :
    thinRotFun T Y M x = (T ^ (-(2 * (M : ℤ) + 1))) x := by
  unfold thinRotFun
  rw [if_neg hx, if_pos hQ]

theorem thinRotFun_of_not {x : X} (hx : x ∉ thin T Y M) (hQ : (T ^ (-((M : ℤ) + 1))) x ∉ Y) :
    thinRotFun T Y M x = x := by
  unfold thinRotFun
  rw [if_neg hx, if_neg hQ]

theorem thinRotInvFun_of_mem {x : X} (hx : (T ^ (-1 : ℤ)) x ∈ thin T Y M) :
    thinRotInvFun T Y M x = (T ^ (-1 : ℤ)) x := by
  unfold thinRotInvFun
  rw [if_pos hx]

theorem thinRotInvFun_of_top {x : X} (hx : (T ^ (-1 : ℤ)) x ∉ thin T Y M)
    (hR : (T ^ (M : ℤ)) x ∈ Y) : thinRotInvFun T Y M x = (T ^ (2 * (M : ℤ) + 1)) x := by
  unfold thinRotInvFun
  rw [if_neg hx, if_pos hR]

theorem thinRotInvFun_of_not {x : X} (hx : (T ^ (-1 : ℤ)) x ∉ thin T Y M)
    (hR : (T ^ (M : ℤ)) x ∉ Y) : thinRotInvFun T Y M x = x := by
  unfold thinRotInvFun
  rw [if_neg hx, if_neg hR]

/-- The top level `M + 1` does not meet `thin T Y M`. -/
theorem notMem_thin_of_top (hY : Wandering T Y L) (hML : 2 * M + 1 ≤ L) {x : X}
    (hQ : (T ^ (-((M : ℤ) + 1))) x ∈ Y) : x ∉ thin T Y M := by
  intro hx
  obtain ⟨k, h1, h2, hk⟩ := mem_thin.mp hx
  exact hY.notMem (a := -((M : ℤ) + 1)) (b := k) (by omega) (by omega) (by omega) hQ hk

theorem thinRotInvFun_thinRotFun (hY : Wandering T Y L) (hML : 2 * M + 1 ≤ L) (x : X) :
    thinRotInvFun T Y M (thinRotFun T Y M x) = x := by
  by_cases hP : x ∈ thin T Y M
  · have e : (T ^ (-1 : ℤ)) ((T ^ (1 : ℤ)) x) = x := by
      rw [zpow_apply_zpow_apply_of_eq T (-1) 1 0 (by norm_num) x, homeo_zpow_zero_apply]
    have h1 : (T ^ (-1 : ℤ)) ((T ^ (1 : ℤ)) x) ∈ thin T Y M := by
      rw [e]
      exact hP
    rw [thinRotFun_of_mem hP, thinRotInvFun_of_mem h1, e]
  · by_cases hQ : (T ^ (-((M : ℤ) + 1))) x ∈ Y
    · have hz2 : (T ^ (M : ℤ)) ((T ^ (-(2 * (M : ℤ) + 1))) x) ∈ Y := by
        rw [zpow_apply_zpow_apply_of_eq T (M : ℤ) (-(2 * (M : ℤ) + 1)) (-((M : ℤ) + 1)) (by ring)
          x]
        exact hQ
      have hz1 : (T ^ (-1 : ℤ)) ((T ^ (-(2 * (M : ℤ) + 1))) x) ∉ thin T Y M := by
        intro h
        obtain ⟨k, h1, h2, hk⟩ := mem_thin.mp h
        rw [zpow_apply_zpow_apply_of_eq T (-1) (-(2 * (M : ℤ) + 1)) (-(2 * (M : ℤ) + 2)) (by ring)
          x, zpow_apply_zpow_apply_of_eq T k (-(2 * (M : ℤ) + 2)) (k - 2 * (M : ℤ) - 2) (by ring)
          x] at hk
        exact hY.notMem (a := -((M : ℤ) + 1)) (b := k - 2 * (M : ℤ) - 2) (by omega) (by omega)
          (by omega) hQ hk
      rw [thinRotFun_of_top hP hQ, thinRotInvFun_of_top hz1 hz2,
        zpow_apply_zpow_apply_of_eq T (2 * (M : ℤ) + 1) (-(2 * (M : ℤ) + 1)) 0 (by ring) x,
        homeo_zpow_zero_apply]
    · have h1 : (T ^ (-1 : ℤ)) x ∉ thin T Y M := by
        intro h
        obtain ⟨k, hk1, hk2, hk⟩ := mem_thin.mp h
        rw [zpow_apply_zpow_apply_of_eq T k (-1) (k - 1) (by ring) x] at hk
        by_cases hkM : k = -(M : ℤ)
        · have e : k - 1 = -((M : ℤ) + 1) := by omega
          rw [e] at hk
          exact hQ hk
        · exact hP (mem_thin_of (k := k - 1) (by omega) (by omega) hk)
      have h2 : (T ^ (M : ℤ)) x ∉ Y := fun h => hP (mem_thin_of (by omega) (by omega) h)
      rw [thinRotFun_of_not hP hQ, thinRotInvFun_of_not h1 h2]

theorem thinRotFun_thinRotInvFun (hY : Wandering T Y L) (hML : 2 * M + 1 ≤ L) (x : X) :
    thinRotFun T Y M (thinRotInvFun T Y M x) = x := by
  by_cases hP : (T ^ (-1 : ℤ)) x ∈ thin T Y M
  · rw [thinRotInvFun_of_mem hP, thinRotFun_of_mem hP,
      zpow_apply_zpow_apply_of_eq T 1 (-1) 0 (by norm_num) x, homeo_zpow_zero_apply]
  · by_cases hR : (T ^ (M : ℤ)) x ∈ Y
    · have hQw : (T ^ (-((M : ℤ) + 1))) ((T ^ (2 * (M : ℤ) + 1)) x) ∈ Y := by
        rw [zpow_apply_zpow_apply_of_eq T (-((M : ℤ) + 1)) (2 * (M : ℤ) + 1) (M : ℤ) (by ring) x]
        exact hR
      rw [thinRotInvFun_of_top hP hR, thinRotFun_of_top (notMem_thin_of_top hY hML hQw) hQw,
        zpow_apply_zpow_apply_of_eq T (-(2 * (M : ℤ) + 1)) (2 * (M : ℤ) + 1) 0 (by ring) x,
        homeo_zpow_zero_apply]
    · have hPx : x ∉ thin T Y M := by
        intro h
        obtain ⟨k, hk1, hk2, hk⟩ := mem_thin.mp h
        by_cases hkM : k = (M : ℤ)
        · rw [hkM] at hk
          exact hR hk
        · refine hP (mem_thin_of (k := k + 1) (by omega) (by omega) ?_)
          rw [zpow_apply_zpow_apply_of_eq T (k + 1) (-1) k (by ring) x]
          exact hk
      have hQx : (T ^ (-((M : ℤ) + 1))) x ∉ Y := by
        intro h
        refine hP (mem_thin_of (k := -(M : ℤ)) (by omega) (by omega) ?_)
        rw [zpow_apply_zpow_apply_of_eq T (-(M : ℤ)) (-1) (-((M : ℤ) + 1)) (by ring) x]
        exact h
      rw [thinRotInvFun_of_not hP hR, thinRotFun_of_not hPx hQx]

/-- The rotation of the tower over a wandering `Y` (Matui 2006, §4). -/
noncomputable def thinRot (hY : Wandering T Y L) (hML : 2 * M + 1 ≤ L) : Equiv.Perm X where
  toFun := thinRotFun T Y M
  invFun := thinRotInvFun T Y M
  left_inv := thinRotInvFun_thinRotFun hY hML
  right_inv := thinRotFun_thinRotInvFun hY hML

theorem thinRot_apply (hY : Wandering T Y L) (hML : 2 * M + 1 ≤ L) (x : X) :
    thinRot hY hML x = thinRotFun T Y M x :=
  rfl

theorem thinRot_apply_of_mem (hY : Wandering T Y L) (hML : 2 * M + 1 ≤ L) {x : X}
    (hx : x ∈ thin T Y M) : thinRot hY hML x = T x := by
  rw [thinRot_apply, thinRotFun_of_mem hx, zpow_one]

theorem thinRot_supportedIn (hY : Wandering T Y L) (hML : 2 * M + 1 ≤ L) :
    HydeLodha.SupportedIn (thinRot hY hML) (thin T Y (M + 1)) := fun x hx => by
  have hP : x ∉ thin T Y M := fun h => hx (thin_mono (by omega) h)
  have hQ : (T ^ (-((M : ℤ) + 1))) x ∉ Y := fun h => hx (mem_thin_of (by omega) (by omega) h)
  rw [thinRot_apply, thinRotFun_of_not hP hQ]

theorem continuous_thinRotCocycle (hYc : IsClopen Y) (M : ℕ) :
    Continuous (thinRotCocycle T Y M) := by
  exact continuous_ite_of_isClopen (fun x => x ∈ thin T Y M) (isClopen_thin hYc M) continuous_const
    (continuous_ite_of_isClopen (fun x => (T ^ (-((M : ℤ) + 1))) x ∈ Y)
      (hYc.preimage (T ^ (-((M : ℤ) + 1))).continuous) continuous_const continuous_const)

theorem thinRot_mem_fullGroup [CompactSpace X] [T2Space X] (hYc : IsClopen Y)
    (hY : Wandering T Y L) (hML : 2 * M + 1 ≤ L) : thinRot hY hML ∈ fullGroup T := by
  refine mem_fullGroup.mpr ⟨thinRotCocycle T Y M, continuous_thinRotCocycle hYc M, fun x => ?_⟩
  rw [thinRot_apply]
  unfold thinRotCocycle
  by_cases hP : x ∈ thin T Y M
  · rw [thinRotFun_of_mem hP, if_pos hP]
  · by_cases hQ : (T ^ (-((M : ℤ) + 1))) x ∈ Y
    · rw [thinRotFun_of_top hP hQ, if_neg hP, if_pos hQ]
    · rw [thinRotFun_of_not hP hQ, if_neg hP, if_neg hQ, homeo_zpow_zero_apply]

/-- **Commutators with `T`** (Matui 2006, Lemma 3.4 and §4; tex l.307–315): for `r ∈ [[T]]`
supported in `thin T Y M` with `6M + 8 ≤ L`, `⁅T, r⁆ ∈ alternatingFullGroup T`. -/
theorem commutatorElement_toEquiv_mem [CompactSpace X] [T2Space X] (hYc : IsClopen Y)
    (hY : Wandering T Y L) (hML : 6 * M + 8 ≤ L) {r : Equiv.Perm X} (hr : r ∈ fullGroup T)
    (hrZ : HydeLodha.SupportedIn r (thin T Y M)) : ⁅T.toEquiv, r⁆ ∈ alternatingFullGroup T := by
  have hML' : 2 * M + 1 ≤ L := by omega
  have hc : T.toEquiv * r * T.toEquiv⁻¹ = thinRot hY hML' * r * (thinRot hY hML')⁻¹ :=
    HydeLodha.conj_eq_of_eqOn hrZ fun x hx => (thinRot_apply_of_mem hY hML' hx).symm
  rw [commutatorElement_def, hc, ← commutatorElement_def]
  exact commutatorElement_mem_of_supportedIn_thin hYc hY (K := M + 1) (by omega)
    (thinRot_mem_fullGroup hYc hY hML') hr (thinRot_supportedIn hY hML')
    (hrZ.mono (thin_mono (by omega)))

end Matui
end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.thinRot_mem_fullGroup
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.commutatorElement_toEquiv_mem
