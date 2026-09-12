import GroupApproximation.CharClass.OddPCompBReal

/-!
# The realisation `compBSum`: degree, and its value in simplex degree `0`

Two of the facts lx-cartan-b's `OddPCompB` consumes about `compBSum p X n σ` (`OddPCompBReal.lean`):

* `compBSum_mem_range` (CB4) — on `ψ_W(e_j)` it lies in total degree `j + n`;
* `compBSum_zero_psiW_zero` (CB6) — on a point and `ψ_W(e_0) = e_0 ⊗ e_0` it is the constant
  `2p`-tuple of the point.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

section Props

variable (p : ℕ) [NeZero p] [Fact p.Prime] (X : TopCat.{0})

/-! ## 1. Degree -/

theorem phiG_mem_range (a m : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop m ⟶ X) :
    CompBReal.phiG p X a m c τ ∈ LinearMap.range (tupIncl (ZMod p) X p (a + m)) :=
  LinearMap.mem_range.mpr ⟨_, (CompBReal.phiG_eq p X a m c τ).symm⟩

/-- `R` on one bidegree `(a, b)` of `W ⊗ W`, for simplices of degrees `m₁`, `m₂`, has total degree
`a + m₁ + (b + m₂)`. -/
theorem realR_atBideg_mem_range (m₁ : ℕ) (τ₁ : stdSimplexTop m₁ ⟶ X) (m₂ : ℕ)
    (τ₂ : stdSimplexTop m₂ ⟶ X) (a b : ℕ) (r : GroupRingZMod2 p) :
    CompBReal.realR p X m₁ τ₁ m₂ τ₂ (wdAtBideg p a b r)
      ∈ LinearMap.range (tupIncl (ZMod p) X (2 * p) (a + m₁ + (b + m₂))) := by
  induction r using MonoidAlgebra.induction_on with
  | hM g =>
    rw [MonoidAlgebra.of_apply, wdAtBideg_single, CompBReal.realR_single]
    exact Submodule.smul_mem _ _
      (tupConcatSq_mem_range (ZMod p) (phiG_mem_range p X _ _ _ _) (phiG_mem_range p X _ _ _ _))
  | hadd x y hx hy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy
  | hsmul c x hx =>
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ c hx

theorem realRT_psiW_mem_range (t₁ t₂ : TagSimp X) (j : ℕ) (x : GroupRingZMod p) :
    CompBReal.realRT p X t₁ t₂ (psiW p j x)
      ∈ LinearMap.range (tupIncl (ZMod p) X (2 * p) (j + (t₁.1 + t₂.1))) := by
  rw [psiW_apply, map_sum]
  refine Submodule.sum_mem _ fun ab hab => ?_
  have hab' : ab.1 + ab.2 = j := Finset.mem_antidiagonal.mp hab
  rw [show j + (t₁.1 + t₂.1) = ab.1 + t₁.1 + (ab.2 + t₂.1) by omega]
  exact realR_atBideg_mem_range p X _ _ _ _ ab.1 ab.2 _

/-- **CB4: the realisation on `ψ_W(e_j)` has total degree `j + n`.** -/
theorem compBSum_mem_range (n : ℕ) (σ : singularSimplices X n) (j : ℕ) (x : GroupRingZMod p) :
    compBSum p X n σ (psiW p j x) ∈ LinearMap.range (tupIncl (ZMod p) X (2 * p) (j + n)) := by
  simp only [compBSum, LinearMap.flip_apply]
  rw [awTupAll_single, map_sum]
  refine Submodule.sum_mem _ fun c hc => ?_
  rw [CompBReal.realRPair_single]
  have hsum : ∑ s : Fin 2, (awTupOf (fun _ : Fin 1 => (⟨n, σ⟩ : TagSimp X)) c s).1
      = ∑ i : Fin 1, ((fun _ : Fin 1 => (⟨n, σ⟩ : TagSimp X)) i).1 :=
    sum_awTupOf (fun _ : Fin 1 => (⟨n, σ⟩ : TagSimp X)) hc
  simp only [Fin.sum_univ_two, Fin.sum_univ_one] at hsum
  have h := realRT_psiW_mem_range p X (awTupOf (fun _ : Fin 1 => (⟨n, σ⟩ : TagSimp X)) c 0)
    (awTupOf (fun _ : Fin 1 => (⟨n, σ⟩ : TagSimp X)) c 1) j x
  rwa [hsum] at h

/-! ## 2. Simplex degree `0` -/

theorem monoGen_zero : CompBReal.monoGen p (0 : ZMod p) = 1 := by
  unfold CompBReal.monoGen
  rw [ofAdd_zero, MonoidAlgebra.one_def]

theorem psiW_zero_one : psiW p 0 1 = Finsupp.single ((0, 0, 0, 0) : WWIdx p) 1 := by
  rw [psiW_one, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  show wdAtBideg p 0 0 (wdPhi p 0 0 (wdT1 p) (wdT2 p)) = _
  rw [wdPhi, if_pos Even.zero]
  simp only [MonoidAlgebra.one_def, wdAtBideg_single, Prod.fst_one, Prod.snd_one, toAdd_one]

/-- `Φ` on a point is the constant tuple of the point. -/
theorem phiG_zero_zero_one (σ : singularSimplices X 0) :
    CompBReal.phiG p X 0 0 1 (simplexEquiv X 0 σ)
      = Finsupp.single (fun _ : Fin p => (⟨0, σ⟩ : TagSimp X)) (1 : ZMod p) := by
  show tupIncl (ZMod p) X p 0
    (oddDiagApp p X 0 (Finsupp.single (⟨0, simplexEquiv X 0 σ⟩ : WSIndex 0 X) 1)) = _
  rw [oddDiagApp_zero, tupIncl_single]
  simp only [diagPt, Equiv.symm_apply_apply]

theorem awTupOf_point_zero (σ : singularSimplices X 0) :
    awTupOf (fun _ : Fin 1 => (⟨0, σ⟩ : TagSimp X)) (fun _ => 0) (0 : Fin 2) = ⟨0, σ⟩ := by
  have h := awTupOf_even (fun _ : Fin 1 => (⟨0, σ⟩ : TagSimp X)) (fun _ => 0) (0 : Fin 1)
  rw [show awSlot 1 ((0 : Fin 1), (0 : Fin 2)) = (0 : Fin (2 * 1)) from Fin.ext rfl] at h
  rw [h]
  exact vtx_id_self σ

theorem awTupOf_point_one (σ : singularSimplices X 0) :
    awTupOf (fun _ : Fin 1 => (⟨0, σ⟩ : TagSimp X)) (fun _ => 0) (1 : Fin 2) = ⟨0, σ⟩ := by
  have h := awTupOf_odd (fun _ : Fin 1 => (⟨0, σ⟩ : TagSimp X)) (fun _ => 0) (0 : Fin 1)
  rw [show awSlot 1 ((0 : Fin 1), (1 : Fin 2)) = (1 : Fin (2 * 1)) from Fin.ext rfl] at h
  rw [h]
  show TopPow.vtx σ (0 - 0) (fun j => j + 0) (TopPow.addRight_mono 0) = _
  rw [TopPow.vtx_congr σ (TopPow.addRight_mono 0) monotone_id (by simp) (fun j _ => by simp),
    vtx_id_self]

/-- **CB6: the realisation on a point and `e_0 ⊗ e_0`** is the constant `2p`-tuple of the point. -/
theorem compBSum_zero_psiW_zero (σ : singularSimplices X 0) :
    compBSum p X 0 σ (psiW p 0 1)
      = Finsupp.single (tupAppendSq p (fun _ => (⟨0, σ⟩ : TagSimp X)) (fun _ => ⟨0, σ⟩))
          (1 : ZMod p) := by
  have hcuts : awCuts (fun _ : Fin 1 => (⟨0, σ⟩ : TagSimp X)) = {fun _ => 0} := by
    simp only [awCuts, zero_add, Finset.range_one]
    exact Fintype.piFinset_singleton (fun _ : Fin 1 => (0 : ℕ))
  simp only [compBSum, LinearMap.flip_apply]
  rw [psiW_zero_one, awTupAll_single, hcuts, Finset.sum_singleton, CompBReal.realRPair_single,
    awTupOf_point_zero, awTupOf_point_one]
  show CompBReal.realR p X 0 (simplexEquiv X 0 σ) 0 (simplexEquiv X 0 σ)
    (Finsupp.single ((0, 0, 0, 0) : WWIdx p) 1) = _
  rw [CompBReal.realR_single, mul_zero, pow_zero, one_smul, monoGen_zero]
  show tupConcatSq (ZMod p) X p (CompBReal.phiG p X 0 0 1 (simplexEquiv X 0 σ))
    (CompBReal.phiG p X 0 0 1 (simplexEquiv X 0 σ)) = _
  rw [phiG_zero_zero_one, tupConcatSq_single_single]

end Props

/-! ## 3. Naturality -/

section Natural

variable (p : ℕ) [NeZero p] [Fact p.Prime]

/-- `Φ` on a generator is natural in the space. -/
theorem tupAllMap_phiG {X Y : TopCat.{0}} (f : X ⟶ Y) (a m : ℕ) (c : GroupRingZMod p)
    (τ : stdSimplexTop m ⟶ X) :
    tupAllMap (ZMod p) f p (CompBReal.phiG p X a m c τ) = CompBReal.phiG p Y a m c (τ ≫ f) := by
  have h := LinearMap.congr_fun (tupIncl_comp_tupMap (ZMod p) f (a + m))
    (oddDiagApp p X (a + m)
      (Finsupp.single (⟨⟨m, Nat.lt_succ_of_le (Nat.le_add_left m a)⟩, τ⟩ : WSIndex (a + m) X) c))
  simp only [LinearMap.comp_apply] at h
  rw [CompBReal.phiG_eq, CompBReal.phiG_eq, ← h, oddDiagApp_natural, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  rfl

/-- `R` for two tagged simplices is natural in the space. -/
theorem tupAllMap_realRT {X Y : TopCat.{0}} (f : X ⟶ Y) (t₁ t₂ : TagSimp X) (w : WWAll p) :
    tupAllMap (ZMod p) f (2 * p) (CompBReal.realRT p X t₁ t₂ w)
      = CompBReal.realRT p Y (tagPush f t₁) (tagPush f t₂) w := by
  induction w using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single q c =>
    obtain ⟨a, s, b, s'⟩ := q
    rw [← Finsupp.smul_single_one]
    simp only [map_smul]
    congr 1
    show tupAllMap (ZMod p) f (2 * p)
        (CompBReal.realR p X t₁.1 (simplexEquiv X t₁.1 t₁.2) t₂.1 (simplexEquiv X t₂.1 t₂.2)
          (Finsupp.single ((a, s, b, s') : WWIdx p) 1))
      = CompBReal.realR p Y t₁.1 (simplexEquiv X t₁.1 t₁.2 ≫ f) t₂.1
          (simplexEquiv X t₂.1 t₂.2 ≫ f) (Finsupp.single ((a, s, b, s') : WWIdx p) 1)
    rw [CompBReal.realR_single, CompBReal.realR_single, map_smul]
    congr 1
    show tupAllMap (ZMod p) f (2 * p) (tupConcatSq (ZMod p) X p _ _) = tupConcatSq (ZMod p) Y p _ _
    rw [tupAllMap_tupConcatSq, tupAllMap_phiG, tupAllMap_phiG]

/-- `R` on the pair model is natural in the space. -/
theorem tupAllMap_realRPair {X Y : TopCat.{0}} (f : X ⟶ Y) (w : WWAll p)
    (y : tupAllMod (ZMod p) X 2) :
    tupAllMap (ZMod p) f (2 * p) (CompBReal.realRPair p X w y)
      = CompBReal.realRPair p Y w (tupAllMap (ZMod p) f 2 y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single t c =>
    rw [← Finsupp.smul_single_one]
    simp only [map_smul, CompBReal.realRPair_single, tupAllMap_single]
    congr 1
    exact tupAllMap_realRT p f (t 0) (t 1) w

/-- **CB5: the realisation is natural in the space.** -/
theorem tupAllMap_compBSum {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (σ : singularSimplices X n)
    (w : WWAll p) :
    tupAllMap (ZMod p) f (2 * p) (compBSum p X n σ w) = compBSum p Y n (pushSimplex f n σ) w := by
  simp only [compBSum, LinearMap.flip_apply]
  rw [tupAllMap_realRPair]
  congr 1
  show tupAllMap (ZMod p) f (2 * 1)
    (awTupAll (ZMod p) X 1 (Finsupp.single (fun _ : Fin 1 => (⟨n, σ⟩ : TagSimp X)) 1)) = _
  rw [tupAllMap_awTupAll, tupAllMap_single]
  rfl

end Natural

end

end GroupApproximation.CharClass

open GroupApproximation.CharClass

#audit_axioms compBSum_mem_range
#audit_axioms compBSum_zero_psiW_zero
