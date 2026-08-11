import NonsoficGroupsExist.PropertyTT.FiniteSubgroupAverage

/-!
# Quasi-cocycle rigidity on finite normal subgroups

This is the finite model of the abelian-normal-subgroup argument.  The proof
is entirely quantitative: average the quasi-cocycle on the subgroup, remove
the fixed component, and use an ambient Kazhdan pair.  It is included both as
a reusable theorem and as the exact finite-stage calculation needed by the
later infinite root-subgroup argument.
-/

namespace NonsoficGroupsExist

open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G]

/-- A finite normal subgroup of a Kazhdan group has relative `(TT)/T`.
No amenability or relative-rigidity result is imported. -/
theorem hasRelativeTTmodT_finiteNormal
    (A : Subgroup G) [Finite A] [A.Normal]
    (hT : HasKazhdanPropertyT.{u, v} G) :
    HasRelativeTTmodT.{u, v} G A := by
  intro E _ _ _ rho hno b D hb
  obtain ⟨Q, epsilon, hQ⟩ := hT
  have hQc : IsKazhdanPairComplex.{u, v} G Q epsilon := hQ.toComplex
  let v : E := quasiCocycleAverage b A
  let w : E := v - unitarySubgroupAverage rho A v
  let M : ℝ := ∑ q ∈ Q, ‖b q‖
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg fun q _ ↦ norm_nonneg (b q)
  have hqM (q : G) (hq : q ∈ Q) : ‖b q‖ ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum
      (fun x _ ↦ norm_nonneg (b x)) hq
  have hwmove (g : G) :
      ‖rho g w - w‖ ≤ 2 * ‖b g‖ + 4 * D := by
    let delta : E := rho g v - v
    let c : E := unitarySubgroupAverage rho A (b g) - b g
    let e : E := delta - c
    have he : ‖e‖ ≤ 2 * D := by
      dsimp [e, delta, c, v]
      exact norm_action_quasiCocycleAverage_sub_le hb A g
    have hc : ‖c‖ ≤ 2 * ‖b g‖ := by
      dsimp [c]
      calc
        ‖unitarySubgroupAverage rho A (b g) - b g‖ ≤
            ‖unitarySubgroupAverage rho A (b g)‖ + ‖b g‖ :=
          norm_sub_le _ _
        _ ≤ ‖b g‖ + ‖b g‖ := by
          gcongr
          exact norm_unitarySubgroupAverage_le rho A (b g)
        _ = 2 * ‖b g‖ := by ring
    have hPe : ‖unitarySubgroupAverage rho A e‖ ≤ 2 * D :=
      (norm_unitarySubgroupAverage_le rho A e).trans he
    have hid : rho g w - w =
        c + e - unitarySubgroupAverage rho A e := by
      dsimp [w, e, delta, c]
      rw [map_sub,
        ← unitarySubgroupAverage_equivariant_of_normal rho A v g,
        unitarySubgroupAverage_sub, unitarySubgroupAverage_sub,
        unitarySubgroupAverage_sub,
        unitarySubgroupAverage_idempotent]
      module
    rw [hid]
    calc
      ‖c + e - unitarySubgroupAverage rho A e‖ ≤
          ‖c‖ + ‖e‖ + ‖unitarySubgroupAverage rho A e‖ := by
        exact (norm_sub_le _ _).trans
          (add_le_add (norm_add_le c e) le_rfl)
      _ ≤ 2 * ‖b g‖ + 2 * D + 2 * D := by gcongr
      _ = 2 * ‖b g‖ + 4 * D := by ring
  have hw : ‖w‖ ≤ (2 * M + 4 * D) / epsilon := by
    by_cases hw0 : w = 0
    · rw [hw0, norm_zero]
      exact div_nonneg
        (add_nonneg (mul_nonneg (by norm_num) hM)
          (mul_nonneg (by norm_num) hb.1)) hQc.1.le
    obtain ⟨q, hq, hqmove⟩ :=
      hQc.exists_moved_mul_norm_of_noInvariant rho hno w hw0
    apply (le_div_iff₀ hQc.1).2
    have hqbound : 2 * ‖b q‖ + 4 * D ≤ 2 * M + 4 * D := by
      gcongr
      exact hqM q hq
    exact hqmove.trans ((hwmove q).trans hqbound)
  refine ⟨2 * ((2 * M + 4 * D) / epsilon) + D, ?_, ?_⟩
  · exact add_nonneg
      (mul_nonneg (by norm_num)
        (div_nonneg
          (add_nonneg (mul_nonneg (by norm_num) hM)
            (mul_nonneg (by norm_num) hb.1)) hQc.1.le))
      hb.1
  intro a ha
  let x : A := ⟨a, ha⟩
  have havg := norm_sub_average_sub_action_average_le hb A x
  have hrewrite :
      v - rho a v = w - rho a w := by
    dsimp [w]
    rw [map_sub, unitarySubgroupAverage_fixed rho A v x]
    module
  change ‖b a‖ ≤ _
  have herror : ‖b a - (w - rho a w)‖ ≤ D := by
    rw [← hrewrite]
    simpa [v, x] using havg
  calc
    ‖b a‖ = ‖(b a - (w - rho a w)) + (w - rho a w)‖ := by
      congr 1
      abel
    _ ≤ ‖b a - (w - rho a w)‖ + ‖w - rho a w‖ := norm_add_le _ _
    _ ≤ D + 2 * ‖w‖ := by
      have hunit : ‖rho a w‖ = ‖w‖ := (rho a).norm_map w
      calc
        _ ≤ D + (‖w‖ + ‖rho a w‖) :=
          add_le_add herror (norm_sub_le _ _)
        _ = D + 2 * ‖w‖ := by rw [hunit]; ring
    _ ≤ D + 2 * ((2 * M + 4 * D) / epsilon) := by gcongr
    _ = 2 * ((2 * M + 4 * D) / epsilon) + D := by ring

end NonsoficGroupsExist
