import GroupApproximation.CharClass.OddPCompBRealPair
import GroupApproximation.CharClass.OddPProductAW

/-!
# The realisation `B` of the odd-primary Cartan comparison on one simplex

`B(e_j ⊗ σ) = riffle( Σ_{AW splits σ = σ'·σ''} R_{σ',σ''}(ψ_W(e_j)) )`.  This file is the inner sum,
`compBSum p X n σ : WWAll p →ₗ tupAllMod (ZMod p) X (2p)`, applied to `ψ_W(e_j)` by lx-cartan-b's
`OddPCompB`.

The sum over Alexander–Whitney splits is not written out by hand.  `R` is packaged as a bilinear
map on `(W ⊗ W) ⊗ (C ⊗ C)`, where `C ⊗ C` is the arity-`2` full tuple model, and `compBSum p X n σ`
is that bilinear map applied to the slotwise Alexander–Whitney image `awTupAll 1 σ` (lx-prodaw).
The Leibniz formula for `R` (`OddPCompBRealPair.lean`) then says the pair model's boundary is the
simplicial boundary term, and `tupDAll_awTupAll` turns the boundary of `awTupAll 1 σ` into the
Alexander–Whitney image of `∂σ`.  So the chain-map law needs no face combinatorics at all.

## Main results (names agreed with lx-cartan-b)

* `wwDiagAct_pow_card`, `tupBlockRotAll_pow_card` — both cyclic actions have order dividing `p`.
* `psiW_mul_galAlgHomP` — `ψ_W` is linear over the group ring for the diagonal action.
* `compBSum_wwDiagAct` (CB1), `compBSum_galAlgHomP` (CB2) — equivariance.
* `tupDAll_compBSum_zero`, `tupDAll_compBSum_succ` (CB3) — the chain-map law.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace CompBReal

section Prefix

variable {X : TopCat.{0}}

theorem tupPre_two_zero (t : TupAll X 2) : tupPre t 0 = 0 := by
  rw [tupPre_eq_sum_ite, Fin.sum_univ_two, if_neg (by decide : ¬ (0 : Fin 2) < 0),
    if_neg (by decide : ¬ (1 : Fin 2) < 0), add_zero]

theorem tupPre_two_one (t : TupAll X 2) : tupPre t 1 = (t 0).1 := by
  rw [tupPre_eq_sum_ite, Fin.sum_univ_two, if_pos (by decide : (0 : Fin 2) < 1),
    if_neg (by decide : ¬ (1 : Fin 2) < 1), add_zero]

theorem tupPre_one_zero (t : TupAll X 1) : tupPre t 0 = 0 := by
  rw [tupPre_eq_sum_ite, Fin.sum_univ_one, if_neg (lt_irrefl _)]

end Prefix

section PairModel

variable (p : ℕ) [NeZero p] [Fact p.Prime] (X : TopCat.{0})

/-- `R` for two tagged simplices. -/
def realRT (t₁ t₂ : TagSimp X) : WWAll p →ₗ[ZMod p] tupAllMod (ZMod p) X (2 * p) :=
  realR p X t₁.1 (simplexEquiv X t₁.1 t₁.2) t₂.1 (simplexEquiv X t₂.1 t₂.2)

/-- **`R` on `(W ⊗ W) ⊗ (C ⊗ C)`**: bilinear; a pair of simplices `t` goes to `R_{t 0, t 1}`. -/
def realRPair : WWAll p →ₗ[ZMod p] tupAllMod (ZMod p) X 2 →ₗ[ZMod p] tupAllMod (ZMod p) X (2 * p) :=
  (Finsupp.linearCombination (ZMod p) (fun t : TupAll X 2 => realRT p X (t 0) (t 1))).flip

theorem realRPair_single (w : WWAll p) (t : TupAll X 2) :
    realRPair p X w (Finsupp.single t 1) = realRT p X (t 0) (t 1) w := by
  simp only [realRPair, LinearMap.flip_apply, Finsupp.linearCombination_single, one_smul]

/-- The boundary terms of `R` in the first simplex are the linear combination over its boundary. -/
theorem realRbdL_eq_lc (t₁ t₂ : TagSimp X) (w : WWAll p) :
    realRbdL p X t₁.1 (simplexEquiv X t₁.1 t₁.2) t₂.1 (simplexEquiv X t₂.1 t₂.2) w
      = Finsupp.linearCombination (ZMod p) (fun τ : TagSimp X => realRT p X τ t₂ w)
          (tagBd (ZMod p) X t₁) := by
  obtain ⟨m, σ₁⟩ := t₁
  cases m with
  | zero =>
    rw [tagBd_zero, map_zero]
    rfl
  | succ m' =>
    rw [realRbdL_succ, LinearMap.sum_apply, tagBd_succ_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [LinearMap.smul_apply, map_zsmul, Finsupp.linearCombination_single, one_smul,
      zsmul_neg_one_pow p, faceMap_def, Equiv.symm_apply_apply]
    rfl

/-- The boundary terms of `R` in the second simplex are the linear combination over its boundary. -/
theorem realRbdR_eq_lc (t₁ t₂ : TagSimp X) (w : WWAll p) :
    realRbdR p X t₁.1 (simplexEquiv X t₁.1 t₁.2) t₂.1 (simplexEquiv X t₂.1 t₂.2) w
      = Finsupp.linearCombination (ZMod p) (fun τ : TagSimp X => realRT p X t₁ τ w)
          (tagBd (ZMod p) X t₂) := by
  obtain ⟨m, σ₂⟩ := t₂
  cases m with
  | zero =>
    rw [tagBd_zero, map_zero]
    rfl
  | succ m' =>
    rw [realRbdR_succ, LinearMap.sum_apply, tagBd_succ_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [LinearMap.smul_apply, map_zsmul, Finsupp.linearCombination_single, one_smul,
      zsmul_neg_one_pow p, faceMap_def, Equiv.symm_apply_apply]
    rfl

/-- `R` on the boundary of a basis pair of simplices. -/
theorem realRPair_tupDAll_single (w : WWAll p) (t : TupAll X 2) :
    realRPair p X w (tupDAll (ZMod p) X 2 (Finsupp.single t 1))
      = Finsupp.linearCombination (ZMod p) (fun τ : TagSimp X => realRT p X τ (t 1) w)
          (tagBd (ZMod p) X (t 0))
        + ((-1 : ZMod p) ^ (t 0).1) •
            Finsupp.linearCombination (ZMod p) (fun τ : TagSimp X => realRT p X (t 0) τ w)
              (tagBd (ZMod p) X (t 1)) := by
  rw [tupDAll, LinearMap.sum_apply, Fin.sum_univ_two, slotBd_single, slotBd_single, slotBdGen,
    slotBdGen, map_add, map_smul, map_smul, Finsupp.apply_linearCombination,
    Finsupp.apply_linearCombination, tupPre_two_zero, tupPre_two_one, pow_zero, one_smul]
  congr 1
  · refine tupLC_congr_fun (ZMod p) (fun τ => ?_) _
    show realRPair p X w (Finsupp.single (Function.update t 0 τ) 1) = realRT p X τ (t 1) w
    rw [realRPair_single, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  · congr 1
    refine tupLC_congr_fun (ZMod p) (fun τ => ?_) _
    show realRPair p X w (Finsupp.single (Function.update t 1 τ) 1) = realRT p X (t 0) τ w
    rw [realRPair_single, Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]

/-- **The Leibniz formula on the pair model**, on basis vectors. -/
theorem tupDAll_realRPair_single_single (a : ℕ) (s : ZMod p) (b : ℕ) (s' : ZMod p)
    (t : TupAll X 2) :
    tupDAll (ZMod p) X (2 * p)
        (realRPair p X (Finsupp.single ((a, s, b, s') : WWIdx p) 1) (Finsupp.single t 1))
      = realRPair p X (wwDAll p (Finsupp.single ((a, s, b, s') : WWIdx p) 1)) (Finsupp.single t 1)
        + ((-1 : ZMod p) ^ (a + b)) •
            realRPair p X (Finsupp.single ((a, s, b, s') : WWIdx p) 1)
              (tupDAll (ZMod p) X 2 (Finsupp.single t 1)) := by
  rw [realRPair_single, realRPair_single, realRPair_tupDAll_single]
  show tupDAll (ZMod p) X (2 * p) (realR p X (t 0).1 (simplexEquiv X (t 0).1 (t 0).2) (t 1).1
      (simplexEquiv X (t 1).1 (t 1).2) (Finsupp.single ((a, s, b, s') : WWIdx p) 1)) = _
  rw [tupDAll_realR_single, realRbdL_eq_lc, realRbdR_eq_lc]
  rfl

/-- **The Leibniz formula on the pair model**, for a basis vector of `W ⊗ W`. -/
theorem tupDAll_realRPair_single (a : ℕ) (s : ZMod p) (b : ℕ) (s' : ZMod p)
    (y : tupAllMod (ZMod p) X 2) :
    tupDAll (ZMod p) X (2 * p) (realRPair p X (Finsupp.single ((a, s, b, s') : WWIdx p) 1) y)
      = realRPair p X (wwDAll p (Finsupp.single ((a, s, b, s') : WWIdx p) 1)) y
        + ((-1 : ZMod p) ^ (a + b)) •
            realRPair p X (Finsupp.single ((a, s, b, s') : WWIdx p) 1) (tupDAll (ZMod p) X 2 y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp only [map_zero, smul_zero, add_zero]
  | add y₁ y₂ h₁ h₂ =>
    simp only [map_add, h₁, h₂, smul_add]
    abel
  | single t c =>
    rw [← Finsupp.smul_single_one]
    simp only [map_smul, tupDAll_realRPair_single_single, smul_add]
    rw [smul_comm]

/-- **The Leibniz formula on the pair model**, on one bidegree of `W ⊗ W`. -/
theorem tupDAll_realRPair_atBideg (a b : ℕ) (r : GroupRingZMod2 p) (y : tupAllMod (ZMod p) X 2) :
    tupDAll (ZMod p) X (2 * p) (realRPair p X (wdAtBideg p a b r) y)
      = realRPair p X (wwDAll p (wdAtBideg p a b r)) y
        + ((-1 : ZMod p) ^ (a + b)) •
            realRPair p X (wdAtBideg p a b r) (tupDAll (ZMod p) X 2 y) := by
  induction r using MonoidAlgebra.induction_on with
  | hM g =>
    rw [MonoidAlgebra.of_apply, wdAtBideg_single]
    exact tupDAll_realRPair_single p X a _ b _ y
  | hadd x z hx hz =>
    simp only [map_add, LinearMap.add_apply, hx, hz, smul_add]
    abel
  | hsmul c x hx =>
    simp only [map_smul, LinearMap.smul_apply, hx, smul_add]
    rw [smul_comm]

/-- **The Leibniz formula on the pair model**, on `ψ_W(e_j)`, which is concentrated in total
`W`-degree `j`. -/
theorem tupDAll_realRPair_psiW (j : ℕ) (x : GroupRingZMod p) (y : tupAllMod (ZMod p) X 2) :
    tupDAll (ZMod p) X (2 * p) (realRPair p X (psiW p j x) y)
      = realRPair p X (wwDAll p (psiW p j x)) y
        + ((-1 : ZMod p) ^ j) • realRPair p X (psiW p j x) (tupDAll (ZMod p) X 2 y) := by
  rw [psiW_apply]
  simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [tupDAll_realRPair_atBideg, Finset.mem_antidiagonal.mp hi]

end PairModel

end CompBReal

/-! ## The realisation on one simplex -/

section CompBSum

/-- **The inner sum of the realisation `B` on one simplex**: `R` applied to the Alexander–Whitney
image of `σ`, i.e. `Σ_i R_{σ[0..i], σ[i..n]}`. -/
def compBSum (p : ℕ) [NeZero p] [Fact p.Prime] (X : TopCat.{0}) (n : ℕ)
    (σ : singularSimplices X n) : WWAll p →ₗ[ZMod p] tupAllMod (ZMod p) X (2 * p) :=
  (CompBReal.realRPair p X).flip
    (awTupAll (ZMod p) X 1 (Finsupp.single (fun _ : Fin 1 => (⟨n, σ⟩ : TagSimp X)) 1))

/-- The diagonal action has order dividing `p`, on a basis vector. -/
theorem wwDiagAct_pow_single (p n a : ℕ) (u : ZMod p) (b : ℕ) (v c : ZMod p) :
    (wwDiagAct p ^ n) (Finsupp.single ((a, u, b, v) : WWIdx p) c)
      = Finsupp.single ((a, (n : ZMod p) + u, b, (n : ZMod p) + v) : WWIdx p) c := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply, Nat.cast_zero, zero_add]
  | succ n ih =>
    have h1 : (1 : ZMod p) + ((n : ZMod p) + u) = ((n + 1 : ℕ) : ZMod p) + u := by
      push_cast
      ring
    have h2 : (1 : ZMod p) + ((n : ZMod p) + v) = ((n + 1 : ℕ) : ZMod p) + v := by
      push_cast
      ring
    rw [pow_succ', Module.End.mul_apply, ih]
    simp only [wwDiagAct, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, h1, h2]

/-- **The diagonal action of `T` on `W ⊗ W` has order dividing `p`.** -/
theorem wwDiagAct_pow_card (p : ℕ) [NeZero p] : wwDiagAct p ^ p = 1 := by
  apply Finsupp.lhom_ext'
  rintro ⟨a, u, b, v⟩
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  rw [wwDiagAct_pow_single, ZMod.natCast_self, zero_add, zero_add]

theorem tupBlockRotAll_pow_tupConcatSq (p : ℕ) (X : TopCat.{0}) (n : ℕ)
    (x y : tupAllMod (ZMod p) X p) :
    (tupBlockRotAll (ZMod p) X p ^ n) (tupConcatSq (ZMod p) X p x y)
      = tupConcatSq (ZMod p) X p ((tupTAll (ZMod p) X p ^ n) x) ((tupTAll (ZMod p) X p ^ n) y) := by
  induction n generalizing x y with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, tupBlockRotAll_tupConcatSq, ih, pow_succ, pow_succ,
      Module.End.mul_apply, Module.End.mul_apply]

/-- **The blockwise rotation has order dividing `p`.** -/
theorem tupBlockRotAll_pow_card (p : ℕ) [NeZero p] (X : TopCat.{0}) :
    tupBlockRotAll (ZMod p) X p ^ p = 1 := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  have ht : t = tupAppendSq p (fun a => t (leftIdx p a)) (fun b => t (rightIdx p b)) :=
    fin_two_mul_funext (fun a => (tupAppendSq_leftIdx _ _ a).symm)
      (fun b => (tupAppendSq_rightIdx _ _ b).symm)
  rw [ht, ← tupConcatSq_single_single, tupBlockRotAll_pow_tupConcatSq, tupTAll_pow_card,
    Module.End.one_apply, Module.End.one_apply]

theorem psiW_grGen_pow_mul (p j n : ℕ) (x : GroupRingZMod p) :
    psiW p j (grGen p ^ n * x) = (wwDiagAct p ^ n) (psiW p j x) := by
  induction n with
  | zero => rw [pow_zero, one_mul, pow_zero, Module.End.one_apply]
  | succ n ih => rw [pow_succ', mul_assoc, psiW_grGen_mul, ih, pow_succ', Module.End.mul_apply]

/-- **`ψ_W` is linear over the group ring** for the diagonal action. -/
theorem psiW_mul_galAlgHomP (p : ℕ) [NeZero p] (j : ℕ) (c x : GroupRingZMod p) :
    psiW p j (c * x) = galAlgHomP (wwDiagAct p) (wwDiagAct_pow_card p) c (psiW p j x) := by
  induction c using MonoidAlgebra.induction_on with
  | hM g =>
    have hV : galAlgHomP (wwDiagAct p) (wwDiagAct_pow_card p)
        (MonoidAlgebra.of (ZMod p) (Multiplicative (ZMod p)) g)
          = galEndP (wwDiagAct p) (wwDiagAct_pow_card p) g := by
      unfold galAlgHomP
      exact MonoidAlgebra.lift_of _ _
    have hg : MonoidAlgebra.of (ZMod p) (Multiplicative (ZMod p)) g
        = grGen p ^ (Multiplicative.toAdd g).val := by
      rw [MonoidAlgebra.of_apply, ← CompBReal.monoGen_eq_pow]
      simp only [CompBReal.monoGen, ofAdd_toAdd]
    rw [hV, hg, psiW_grGen_pow_mul]
    rfl
  | hadd c₁ c₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, LinearMap.add_apply]
  | hsmul r c h => rw [smul_mul_assoc, map_smul, h, map_smul, LinearMap.smul_apply]

variable (p : ℕ) [NeZero p] [Fact p.Prime] (X : TopCat.{0})

/-- **CB1: the diagonal action goes to the blockwise rotation.** -/
theorem compBSum_wwDiagAct (n : ℕ) (σ : singularSimplices X n) (w : WWAll p) :
    compBSum p X n σ (wwDiagAct p w) = tupBlockRotAll (ZMod p) X p (compBSum p X n σ w) := by
  simp only [compBSum, LinearMap.flip_apply]
  generalize awTupAll (ZMod p) X 1 (Finsupp.single (fun _ : Fin 1 => (⟨n, σ⟩ : TagSimp X)) 1) = y
  induction y using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single t c =>
    rw [← Finsupp.smul_single_one]
    simp only [map_smul, CompBReal.realRPair_single]
    congr 1
    exact CompBReal.realR_wwDiagAct p X _ _ _ _ w

/-- **CB2: equivariance over the group ring.** -/
theorem compBSum_galAlgHomP (n : ℕ) (σ : singularSimplices X n) (c : GroupRingZMod p)
    (w : WWAll p) :
    compBSum p X n σ (galAlgHomP (wwDiagAct p) (wwDiagAct_pow_card p) c w)
      = galAlgHomP (tupBlockRotAll (ZMod p) X p) (tupBlockRotAll_pow_card p X) c
          (compBSum p X n σ w) :=
  galAlgHomP_comm p (wwDiagAct p) (wwDiagAct_pow_card p) (tupBlockRotAll (ZMod p) X p)
    (tupBlockRotAll_pow_card p X) (compBSum p X n σ) (fun v => compBSum_wwDiagAct p X n σ v) c w

/-- **CB3, simplex degree `0`**: the realisation commutes with the differentials. -/
theorem tupDAll_compBSum_zero (σ : singularSimplices X 0) (w : WWAll p) :
    tupDAll (ZMod p) X (2 * p) (compBSum p X 0 σ w) = compBSum p X 0 σ (wwDAll p w) := by
  simp only [compBSum, LinearMap.flip_apply]
  have hy : tupDAll (ZMod p) X 2
      (awTupAll (ZMod p) X 1 (Finsupp.single (fun _ : Fin 1 => (⟨0, σ⟩ : TagSimp X)) 1)) = 0 := by
    show tupDAll (ZMod p) X (2 * 1)
      (awTupAll (ZMod p) X 1 (Finsupp.single (fun _ : Fin 1 => (⟨0, σ⟩ : TagSimp X)) 1)) = 0
    rw [tupDAll_awTupAll, tupDAll_single_of_tot_eq_zero (ZMod p)
      (fun _ : Fin 1 => (⟨0, σ⟩ : TagSimp X)) (by simp), map_zero]
  induction w using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add w₁ w₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | single q c =>
    obtain ⟨a, s, b, s'⟩ := q
    rw [← Finsupp.smul_single_one]
    simp only [map_smul, LinearMap.smul_apply]
    rw [CompBReal.tupDAll_realRPair_single, hy, map_zero, smul_zero, add_zero]

/-- The boundary of a single `(n+1)`-simplex in the arity-`1` model, as a face sum. -/
theorem tupDAll_one_single_succ (n : ℕ) (σ : singularSimplices X (n + 1)) :
    tupDAll (ZMod p) X 1 (Finsupp.single (fun _ : Fin 1 => (⟨n + 1, σ⟩ : TagSimp X)) 1)
      = ∑ f : Fin (n + 2), ((-1 : ZMod p) ^ (f : ℕ)) •
          Finsupp.single (fun _ : Fin 1 => (⟨n, faceSimplex X n f σ⟩ : TagSimp X)) (1 : ZMod p) := by
  rw [tupDAll, LinearMap.sum_apply, Fin.sum_univ_one, slotBd_single, slotBdGen,
    CompBReal.tupPre_one_zero, pow_zero, one_smul, tagBd_succ_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [map_zsmul, Finsupp.linearCombination_single, one_smul, CompBReal.zsmul_neg_one_pow p,
    show Function.update (fun _ : Fin 1 => (⟨n + 1, σ⟩ : TagSimp X)) 0
        (⟨n, faceSimplex X n f σ⟩ : TagSimp X) = fun _ => ⟨n, faceSimplex X n f σ⟩ from
      funext fun i => by rw [Fin.fin_one_eq_zero i, Function.update_self]]

/-- **CB3, positive simplex degree**: the realisation on `ψ_W(e_j)` commutes with the differentials up
to the Alexander–Whitney boundary term. -/
theorem tupDAll_compBSum_succ (n : ℕ) (σ : singularSimplices X (n + 1)) (j : ℕ)
    (x : GroupRingZMod p) :
    tupDAll (ZMod p) X (2 * p) (compBSum p X (n + 1) σ (psiW p j x))
      = compBSum p X (n + 1) σ (wwDAll p (psiW p j x))
        + (-1 : ZMod p) ^ j •
            ∑ f : Fin (n + 2), (-1 : ZMod p) ^ (f : ℕ) •
              compBSum p X n (faceSimplex X n f σ) (psiW p j x) := by
  simp only [compBSum, LinearMap.flip_apply]
  rw [CompBReal.tupDAll_realRPair_psiW]
  congr 2
  have hd : tupDAll (ZMod p) X 2
      (awTupAll (ZMod p) X 1 (Finsupp.single (fun _ : Fin 1 => (⟨n + 1, σ⟩ : TagSimp X)) 1))
        = ∑ f : Fin (n + 2), ((-1 : ZMod p) ^ (f : ℕ)) •
            awTupAll (ZMod p) X 1
              (Finsupp.single (fun _ : Fin 1 => (⟨n, faceSimplex X n f σ⟩ : TagSimp X)) 1) := by
    show tupDAll (ZMod p) X (2 * 1)
      (awTupAll (ZMod p) X 1 (Finsupp.single (fun _ : Fin 1 => (⟨n + 1, σ⟩ : TagSimp X)) 1)) = _
    rw [tupDAll_awTupAll, tupDAll_one_single_succ, map_sum]
    exact Finset.sum_congr rfl fun f _ => map_smul _ _ _
  rw [hd, map_sum]
  exact Finset.sum_congr rfl fun f _ => map_smul _ _ _

end CompBSum

end

end GroupApproximation.CharClass

open GroupApproximation.CharClass

#audit_axioms wwDiagAct_pow_card
#audit_axioms tupBlockRotAll_pow_card
#audit_axioms psiW_mul_galAlgHomP
#audit_axioms compBSum_wwDiagAct
#audit_axioms compBSum_galAlgHomP
#audit_axioms tupDAll_compBSum_zero
#audit_axioms tupDAll_compBSum_succ
