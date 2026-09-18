import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.CrossedProductCovariant

/-!
# Matrix units on `ℓ²(G, H)` and the amplification of a representation

Lane TWWUCT-A (work order WO-TWWUCT-A), `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input).  This is the first half of the proof that
the norm of the reduced crossed product does not depend on the faithful representation
(Brown--Ozawa, Prop. 4.1.5; Williams, Lemma 7.7).  For a finite set `F ⊆ G`:

* `matEntry s t T = e_{st} ⊗ T`, `ξ ↦ δ_s ⊗ T (ξ t)`, with `(e_{st} ⊗ T)⋆ = e_{ts} ⊗ T⋆`;
* `trunc F = ∑_{s ∈ F} e_{ss} ⊗ 1`, a contraction with `trunc F ξ → ξ` along finite sets;
* `matRep ρ F : M_F(A) → B(ℓ²(G, H))`, `M ↦ ∑_{s,t ∈ F} e_{st} ⊗ ρ(M_{st})`, a
  `⋆`-homomorphism, injective whenever `ρ` is.
-/

namespace GroupApproximation.Full.TWWUCT.CrossedProduct

open scoped InnerProductSpace Topology

universe u v w

noncomputable section

variable {G : Type u} [DecidableEq G]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## Matrix units -/

/-- The matrix unit `e_{st} ⊗ T` on `ℓ²(G, H)`: `ξ ↦ δ_s ⊗ T (ξ t)`. -/
def matEntry (s t : G) : (H →L[ℂ] H) →ₗ[ℂ] (L2 G H →L[ℂ] L2 G H) where
  toFun T := (lp.singleContinuousLinearMap ℂ (fun _ : G => H) 2 s).comp
    (T.comp (lp.evalCLM ℂ (fun _ : G => H) 2 t))
  map_add' T T' := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    change (lp.single 2 s ((T + T') (ξ t)) : L2 G H) =
      lp.single 2 s (T (ξ t)) + lp.single 2 s (T' (ξ t))
    rw [ContinuousLinearMap.add_apply, lp.single_add]
  map_smul' c T := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    change (lp.single 2 s ((c • T) (ξ t)) : L2 G H) = c • lp.single 2 s (T (ξ t))
    rw [ContinuousLinearMap.smul_apply, lp.single_smul]

theorem matEntry_apply (s t : G) (T : H →L[ℂ] H) (ξ : L2 G H) :
    matEntry s t T ξ = (lp.single 2 s (T (ξ t)) : L2 G H) :=
  rfl

theorem star_matEntry [CompleteSpace H] (s t : G) (T : H →L[ℂ] H) :
    star (matEntry (H := H) s t T) = matEntry t s (star T) := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro ξ η
  rw [matEntry_apply, matEntry_apply, lp.inner_single_left, lp.inner_single_right,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-! ## Truncation to a finite set -/

/-- The coordinate projection `trunc F = ∑_{s ∈ F} e_{ss} ⊗ 1` onto `ℓ²(F, H)`. -/
def trunc (F : Finset G) : L2 G H →L[ℂ] L2 G H :=
  ∑ s ∈ F, matEntry s s (1 : H →L[ℂ] H)

theorem trunc_apply (F : Finset G) (ξ : L2 G H) :
    trunc F ξ = ∑ s ∈ F, (lp.single 2 s (ξ s) : L2 G H) := by
  rw [trunc, _root_.sum_apply]
  exact Finset.sum_congr rfl fun s _ => rfl

theorem trunc_apply_apply (F : Finset G) (ξ : L2 G H) (r : G) :
    trunc F ξ r = if r ∈ F then ξ r else 0 := by
  rw [trunc_apply, lp.coeFn_sum, Finset.sum_apply]
  exact Finset.sum_pi_single r (fun s => ξ s) F

theorem norm_trunc_apply_le (F : Finset G) (ξ : L2 G H) : ‖trunc F ξ‖ ≤ ‖ξ‖ := by
  refine lp.norm_mono (by norm_num) fun r => ?_
  rw [trunc_apply_apply]
  split_ifs
  · exact le_rfl
  · rw [norm_zero]
    exact norm_nonneg _

theorem norm_trunc_le (F : Finset G) : ‖trunc (H := H) F‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => by
    rw [one_mul]
    exact norm_trunc_apply_le F ξ

/-- `trunc F ξ → ξ` along the finite subsets of `G`. -/
theorem tendsto_trunc (ξ : L2 G H) :
    Filter.Tendsto (fun F : Finset G => trunc F ξ) Filter.atTop (𝓝 ξ) := by
  have h : Filter.Tendsto (fun F : Finset G => ∑ i ∈ F, (lp.single 2 i (ξ i) : L2 G H))
      Filter.atTop (𝓝 ξ) :=
    lp.hasSum_single (E := fun _ : G => H) (p := 2) ENNReal.two_ne_top ξ
  have hfun : (fun F : Finset G => trunc F ξ) =
      fun F : Finset G => ∑ i ∈ F, (lp.single 2 i (ξ i) : L2 G H) :=
    funext fun F => trunc_apply F ξ
  rw [hfun]
  exact h

/-! ## The amplification `M_F(A) → B(ℓ²(G, H))` -/

variable {A : Type v} [NonUnitalCStarAlgebra A]
variable (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- The operator `∑_{s,t ∈ F} e_{st} ⊗ ρ(M_{st})` on `ℓ²(G, H)`. -/
def matOp (F : Finset G) (M : CStarMatrix F F A) : L2 G H →L[ℂ] L2 G H :=
  ∑ s : F, ∑ t : F, matEntry (s : G) (t : G) (ρ (M s t))

theorem matOp_apply_apply (F : Finset G) (M : CStarMatrix F F A) (ξ : L2 G H) (r : G) :
    matOp ρ F M ξ r = ∑ s : F, ∑ t : F, Pi.single (s : G) (ρ (M s t) (ξ t)) r := by
  rw [matOp, _root_.sum_apply, lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [_root_.sum_apply, lp.coeFn_sum, Finset.sum_apply]
  rfl

theorem matOp_apply_of_mem (F : Finset G) (M : CStarMatrix F F A) (ξ : L2 G H) {r : G}
    (hr : r ∈ F) : matOp ρ F M ξ r = ∑ t : F, ρ (M ⟨r, hr⟩ t) (ξ t) := by
  rw [matOp_apply_apply, Finset.sum_eq_single ⟨r, hr⟩]
  · exact Finset.sum_congr rfl fun t _ => Pi.single_eq_same r _
  · intro s _ hs
    refine Finset.sum_eq_zero fun t _ => ?_
    exact Pi.single_eq_of_ne (fun h => hs (Subtype.ext h.symm)) _
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem matOp_apply_coe (F : Finset G) (M : CStarMatrix F F A) (ξ : L2 G H) (s : F) :
    matOp ρ F M ξ s = ∑ t : F, ρ (M s t) (ξ t) :=
  matOp_apply_of_mem ρ F M ξ s.2

theorem matOp_apply_of_notMem (F : Finset G) (M : CStarMatrix F F A) (ξ : L2 G H) {r : G}
    (hr : r ∉ F) : matOp ρ F M ξ r = 0 := by
  rw [matOp_apply_apply]
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
  refine Pi.single_eq_of_ne (fun h => hr ?_) _
  rw [h]
  exact s.2

variable [CompleteSpace H]

/-- **The amplification** `M_F(A) → B(ℓ²(G, H))`, `M ↦ ∑_{s,t ∈ F} e_{st} ⊗ ρ(M_{st})`,
a `⋆`-homomorphism (Brown--Ozawa, proof of Prop. 4.1.5).  `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input). -/
def matRep (F : Finset G) : CStarMatrix F F A →⋆ₙₐ[ℂ] (L2 G H →L[ℂ] L2 G H) where
  toFun := matOp ρ F
  map_smul' c M := by
    change matOp ρ F (c • M) = c • matOp ρ F M
    unfold matOp
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [CStarMatrix.smul_apply, map_smul, map_smul]
  map_zero' := by
    change matOp ρ F 0 = 0
    unfold matOp
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
    rw [CStarMatrix.zero_apply, map_zero, map_zero]
  map_add' M N := by
    change matOp ρ F (M + N) = matOp ρ F M + matOp ρ F N
    unfold matOp
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [CStarMatrix.add_apply, map_add, map_add]
  map_mul' M N := by
    refine ContinuousLinearMap.ext fun ξ => lp.ext (funext fun r => ?_)
    change matOp ρ F (M * N) ξ r = matOp ρ F M (matOp ρ F N ξ) r
    by_cases hr : r ∈ F
    · rw [matOp_apply_of_mem ρ F (M * N) ξ hr, matOp_apply_of_mem ρ F M _ hr]
      have hL : ∀ u : F, ρ ((M * N) ⟨r, hr⟩ u) (ξ u) =
          ∑ t : F, ρ (M ⟨r, hr⟩ t) (ρ (N t u) (ξ u)) := fun u => by
        change ρ (∑ t : F, M ⟨r, hr⟩ t * N t u) (ξ u) = _
        rw [map_sum, _root_.sum_apply]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [map_mul, ContinuousLinearMap.mul_apply]
      have hR : ∀ t : F, ρ (M ⟨r, hr⟩ t) (matOp ρ F N ξ t) =
          ∑ u : F, ρ (M ⟨r, hr⟩ t) (ρ (N t u) (ξ u)) := fun t => by
        rw [matOp_apply_coe, map_sum]
      calc ∑ u : F, ρ ((M * N) ⟨r, hr⟩ u) (ξ u)
          = ∑ u : F, ∑ t : F, ρ (M ⟨r, hr⟩ t) (ρ (N t u) (ξ u)) :=
            Finset.sum_congr rfl fun u _ => hL u
        _ = ∑ t : F, ∑ u : F, ρ (M ⟨r, hr⟩ t) (ρ (N t u) (ξ u)) := Finset.sum_comm
        _ = ∑ t : F, ρ (M ⟨r, hr⟩ t) (matOp ρ F N ξ t) :=
            Finset.sum_congr rfl fun t _ => (hR t).symm
    · rw [matOp_apply_of_notMem ρ F _ _ hr, matOp_apply_of_notMem ρ F _ _ hr]
  map_star' M := by
    change matOp ρ F (star M) = star (matOp ρ F M)
    unfold matOp
    rw [star_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [star_matEntry, CStarMatrix.star_apply, map_star]

theorem matRep_apply (F : Finset G) (M : CStarMatrix F F A) : matRep ρ F M = matOp ρ F M :=
  rfl

/-- The amplification of an injective representation is injective. -/
theorem matRep_injective {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : Function.Injective π)
    (F : Finset G) : Function.Injective (matRep π F) := by
  refine (injective_iff_map_eq_zero (matRep π F)).2 fun M hM => ?_
  refine CStarMatrix.ext fun s t => ?_
  refine (injective_iff_map_eq_zero π).1 hπ _ (ContinuousLinearMap.ext fun v => ?_)
  have h := congrArg (fun T : L2 G H →L[ℂ] L2 G H => T (lp.single 2 (t : G) v) (s : G)) hM
  change matOp π F M (lp.single 2 (t : G) v) s =
    (0 : L2 G H →L[ℂ] L2 G H) (lp.single 2 (t : G) v) s at h
  rw [matOp_apply_coe, ContinuousLinearMap.zero_apply, lp.coeFn_zero, Pi.zero_apply,
    Finset.sum_eq_single t] at h
  · rw [lp.single_apply_self] at h
    rw [ContinuousLinearMap.zero_apply]
    exact h
  · intro u _ hu
    rw [lp.single_apply_ne 2 (t : G) v (fun h => hu (Subtype.ext h)), map_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

end

end GroupApproximation.Full.TWWUCT.CrossedProduct
