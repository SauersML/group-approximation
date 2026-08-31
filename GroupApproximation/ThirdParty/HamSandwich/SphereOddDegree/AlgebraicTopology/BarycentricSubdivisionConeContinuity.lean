import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeDefs

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

theorem continuousOn_coneTail {k : ℕ} :
    ContinuousOn (coneTail (k := k)) {x : Delta (k + 1) | (x : Fin (k + 1 + 1) → ℝ) 0 ≠ 1} := by
  -- Write `S := {x : Delta (k+1) | (x:_) 0 ≠ 1}`.
  set S : Set (Delta (k + 1)) := {x | x 0 ≠ 1};
  have h_cont_tail : ContinuousOn (fun x : Delta (k + 1) => (coneTail x : Fin (k + 1) → ℝ)) S := by
    refine' ContinuousOn.congr _ _;
    exact fun x i => ( x : Fin ( k + 1 + 1 ) → ℝ ) i.succ / ( 1 - ( x : Fin ( k + 1 + 1 ) → ℝ ) 0 );
    · exact continuousOn_pi.mpr fun i => ContinuousOn.div ( continuous_apply _ |> Continuous.comp_continuousOn <| continuous_subtype_val.continuousOn ) ( continuousOn_const.sub <| continuous_apply _ |> Continuous.comp_continuousOn <| continuous_subtype_val.continuousOn ) fun x hx => sub_ne_zero_of_ne <| Ne.symm hx;
    · intro x hx; ext i; exact coneTail_apply x hx i;
  rw [ continuousOn_iff_continuous_restrict ] at *;
  exact continuous_induced_rng.mpr h_cont_tail

/-
The cone of a continuous `τ` over `v` is continuous.
-/
theorem continuous_affineConeMap {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n)) :
    Continuous (affineConeMap v (⇑τ)) := by
  refine' continuous_induced_rng.mpr _;
  refine' continuous_pi fun j => _;
  -- The function $B(x) = (1 - x 0) * ((τ (coneTail x)) j)$ is continuous because it is a product of continuous functions.
  have hB_cont : Continuous (fun x : Delta (k + 1) => (1 - x 0) * ((τ (coneTail x)) j)) := by
    refine' continuous_iff_continuousAt.mpr _;
    intro x;
    by_cases hx : x 0 = 1;
    · refine' tendsto_iff_norm_sub_tendsto_zero.mpr _;
      refine' squeeze_zero ( fun _ => norm_nonneg _ ) ( fun e => _ ) ( Continuous.tendsto' ( show Continuous fun e : Delta ( k + 1 ) => |1 - e 0| from Continuous.abs <| continuous_const.sub <| continuous_apply 0 |> Continuous.comp <| continuous_subtype_val ) _ _ <| by aesop );
      simp +decide [ hx ];
      exact mul_le_of_le_one_right ( abs_nonneg _ ) ( abs_le.mpr ⟨ by linarith [ stdSimplex.zero_le ( τ ( coneTail e ) ) j ], by linarith [ stdSimplex.le_one ( τ ( coneTail e ) ) j ] ⟩ );
    · refine' ContinuousAt.mul _ _;
      · exact ContinuousAt.sub continuousAt_const ( continuousAt_subtype_val.comp continuousAt_id |> ContinuousAt.comp ( continuousAt_apply _ _ ) );
      · refine' ContinuousAt.comp ( continuous_apply j |> Continuous.continuousAt ) _;
        refine' ContinuousAt.comp _ _;
        · exact Continuous.continuousAt ( by continuity );
        · refine' ContinuousAt.comp _ _;
          · exact τ.continuous.continuousAt;
          · exact continuousOn_coneTail.continuousAt ( IsOpen.mem_nhds ( isOpen_compl_singleton.preimage ( continuous_apply 0 |> Continuous.comp <| continuous_subtype_val ) ) hx );
  convert Continuous.add ( Continuous.mul
    (continuous_apply 0 |> Continuous.comp <| continuous_subtype_val)
    (show Continuous (fun _ : Delta (k + 1) => (v : Fin (n + 1) → ℝ) j) from
      continuous_const)) hB_cont using 1
  funext x
  rfl

/-- **The bundled continuous cone map** `Cone_v(τ) : C(Δᵏ⁺¹, Δⁿ)`. -/
noncomputable def affineConeContinuousMap {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n)) :
    C(Delta (k + 1), Delta n) :=
  ⟨affineConeMap v (⇑τ), continuous_affineConeMap v τ⟩

@[simp] theorem affineConeContinuousMap_apply {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n))
    (x : Delta (k + 1)) : affineConeContinuousMap v τ x = affineConeMap v (⇑τ) x := rfl
end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
