import GroupApproximation.CharClass.CartanDiagonalModule
import GroupApproximation.CharClass.AcyclicModels
import Mathlib.Tactic.LinearCombination

/-!
# `W ⊗ S(X)` as a chain complex

`CartanDiagonalModule.lean` gives the degreewise free `Λ`-module and the two
halves of the differential.  This file proves `d ∘ d = 0` and assembles the
chain complex.

## How the cancellation splits

On a generator `e_{k+2-n} ⊗ σ` the composite `d ∘ d` has four pieces, and each
either vanishes on its own or cancels against exactly one other:

* `W` then `W` contributes the scalar `(1 + T)²`, which is `0` because
  `T² = 1` and `2 = 0` (`one_add_gen_sq`);
* `S` then `S` is `∂ ∘ ∂` applied inside a `Finsupp.lmapDomain`, so it vanishes
  by `SingularBoundaryData.bd_bd`;
* `W` then `S` and `S` then `W` are the *same* element — both are
  `(1 + T)` times the boundary chain sitting one simplex-degree down — and
  cancel because `Λ` has characteristic two.

The bookkeeping that makes this readable is the choice of index in
`CartanDiagonalModule`: the `W`-half moves the `Fin` index by `castSucc` and the
`S`-half by `succ`, so the three cases of the induction are exactly
`Fin.cases` on `n` followed by `Fin.lastCases` on its predecessor, with no
arithmetic side conditions and no transport of the simplex.
-/

namespace GroupApproximation.CharClass

open CategoryTheory

noncomputable section

/-! ## 1. Scalars -/

/-- `(1 + T)² = 0`: the square of the differential of the periodic resolution. -/
theorem one_add_gen_sq : (1 + groupRingGen) * (1 + groupRingGen) = 0 := by
  linear_combination groupRingGen_mul_self + (1 + groupRingGen) * two_eq_zero_groupRingZ2

/-- Every `Λ`-module has characteristic two, since `Λ` does. -/
theorem two_smul_eq_zero {M : Type} [AddCommGroup M] [Module GroupRingZ2 M] (x : M) :
    x + x = 0 := by
  rw [← two_smul GroupRingZ2 x, two_eq_zero_groupRingZ2, zero_smul]

/-! ## 2. Three `Finsupp` helpers -/

/-- A linear map is recovered from its values on the basis. -/
theorem linearCombination_comp_single {ι M : Type} [AddCommGroup M]
    [Module GroupRingZ2 M] (F : (ι →₀ GroupRingZ2) →ₗ[GroupRingZ2] M) :
    Finsupp.linearCombination GroupRingZ2
        (fun a => F (Finsupp.single a (1 : GroupRingZ2))) = F := by
  apply Finsupp.lhom_ext'
  intro a
  apply LinearMap.ext_ring
  simp

/-- `Finsupp.linearCombination` is additive in the family of values. -/
theorem linearCombination_add_fun {ι M : Type} [AddCommGroup M]
    [Module GroupRingZ2 M] (v w : ι → M) :
    Finsupp.linearCombination GroupRingZ2 (fun a => v a + w a)
      = Finsupp.linearCombination GroupRingZ2 v
        + Finsupp.linearCombination GroupRingZ2 w := by
  apply Finsupp.lhom_ext'
  intro a
  apply LinearMap.ext_ring
  simp

/-- The zero family gives the zero map. -/
theorem linearCombination_zero_fun {ι M : Type} [AddCommGroup M]
    [Module GroupRingZ2 M] (z : ι →₀ GroupRingZ2) :
    Finsupp.linearCombination GroupRingZ2 (fun _ : ι => (0 : M)) z = 0 := by
  simp [Finsupp.linearCombination_apply]

/-! ## 3. The three cancellations -/

variable (data : SingularBoundaryData) (X : TopCat.{0})

/-- `W` then `W`: the scalar `(1 + T)²` kills it. -/
theorem smul_wDiffW (k : ℕ) (n : Fin (k + 2)) (σ : stdSimplexTop n.val ⟶ X) :
    (1 + groupRingGen) • wDiffW X k n σ = 0 := by
  revert σ
  induction n using Fin.lastCases with
  | last => intro σ; rw [wDiffW_last, smul_zero]
  | cast j =>
      intro σ
      rw [wDiffW_castSucc, smul_smul, one_add_gen_sq, zero_smul]

/-- `wDiff` applied to a chain supported at one simplex degree. -/
theorem wDiff_lmapDomain (k : ℕ) (m : Fin (k + 2))
    (z : (stdSimplexTop m.val ⟶ X) →₀ GroupRingZ2) :
    wDiff data X k (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2
        (fun τ => (⟨m, τ⟩ : WSIndex (k + 1) X)) z)
      = Finsupp.linearCombination GroupRingZ2 (fun τ => wDiffW X k m τ) z
        + Finsupp.linearCombination GroupRingZ2 (fun τ => wDiffS data X k m τ) z := by
  rw [wDiff, Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain]
  have hfun : ((fun p : WSIndex (k + 1) X => wDiffGen data X k p.1 p.2)
        ∘ fun τ => (⟨m, τ⟩ : WSIndex (k + 1) X))
      = fun τ => wDiffW X k m τ + wDiffS data X k m τ := rfl
  rw [hfun, linearCombination_add_fun, LinearMap.add_apply]

/-- `S` then `S`: `∂ ∘ ∂ = 0`. -/
theorem linearCombination_wDiffS_bd (k : ℕ) (m : Fin (k + 2))
    (z : (stdSimplexTop (m.val + 1) ⟶ X) →₀ GroupRingZ2) :
    Finsupp.linearCombination GroupRingZ2 (fun τ => wDiffS data X k m τ)
        (data.bd X m.val z) = 0 := by
  revert z
  induction m using Fin.cases with
  | zero =>
      intro z
      have hfun : (fun τ : stdSimplexTop (0 : Fin (k + 2)).val ⟶ X =>
          wDiffS data X k 0 τ) = fun _ => (0 : WTensorSMod X k) :=
        funext (wDiffS_zero data X k)
      rw [hfun, linearCombination_zero_fun]
  | succ i =>
      intro z
      let F : ((stdSimplexTop (Fin.succ i).val ⟶ X) →₀ GroupRingZ2) →ₗ[GroupRingZ2]
          WTensorSMod X k :=
        (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2
          (fun ρ => (⟨i, ρ⟩ : WSIndex k X))).comp (data.bd X i.val)
      have hfun : (fun τ : stdSimplexTop (Fin.succ i).val ⟶ X =>
            wDiffS data X k (Fin.succ i) τ)
          = fun τ => F (Finsupp.single τ (1 : GroupRingZ2)) := by
        funext τ
        rw [wDiffS_succ]
        rfl
      rw [hfun, linearCombination_comp_single]
      have hbd : data.bd X i.val (data.bd X (Fin.succ i).val z) = 0 :=
        data.bd_bd X i.val z
      show (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2
          (fun ρ => (⟨i, ρ⟩ : WSIndex k X))) (data.bd X i.val
            (data.bd X (Fin.succ i).val z)) = 0
      rw [hbd, map_zero]

/-- `W` then `S` equals `S` then `W`. -/
theorem mixed_terms_eq (k : ℕ) (i : Fin (k + 1))
    (σ : stdSimplexTop (Fin.succ (Fin.castSucc i)).val ⟶ X) :
    (1 + groupRingGen) • wDiffS data X k (Fin.succ i) σ
      = Finsupp.linearCombination GroupRingZ2 (fun τ => wDiffW X k (Fin.castSucc i) τ)
          (data.bd X i.val (Finsupp.single σ (1 : GroupRingZ2))) := by
  let G : ((stdSimplexTop (Fin.castSucc i).val ⟶ X) →₀ GroupRingZ2) →ₗ[GroupRingZ2]
      WTensorSMod X k :=
    (1 + groupRingGen) • Finsupp.lmapDomain GroupRingZ2 GroupRingZ2
      (fun ρ => (⟨i, ρ⟩ : WSIndex k X))
  have hfun : (fun τ : stdSimplexTop (Fin.castSucc i).val ⟶ X =>
        wDiffW X k (Fin.castSucc i) τ)
      = fun τ => G (Finsupp.single τ (1 : GroupRingZ2)) := by
    funext τ
    rw [wDiffW_castSucc]
    show (1 + groupRingGen) • Finsupp.single (⟨i, τ⟩ : WSIndex k X) 1
        = (1 + groupRingGen) • (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2
            (fun ρ => (⟨i, ρ⟩ : WSIndex k X)) (Finsupp.single τ 1))
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [hfun, linearCombination_comp_single, wDiffS_succ]
  show (1 + groupRingGen) • (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2
      (fun τ => (⟨i, τ⟩ : WSIndex k X))
      (data.bd X i.val (Finsupp.single σ (1 : GroupRingZ2))))
    = (1 + groupRingGen) • (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2
      (fun ρ => (⟨i, ρ⟩ : WSIndex k X))
      (data.bd X i.val (Finsupp.single σ (1 : GroupRingZ2))))
  rfl

/-! ## 4. `d ∘ d = 0` -/

/-- **The chain-complex condition.** -/
theorem wDiff_wDiff (k : ℕ) (p : WSIndex (k + 2) X) :
    wDiff data X k (wDiff data X (k + 1) (Finsupp.single p (1 : GroupRingZ2))) = 0 := by
  obtain ⟨n, σ⟩ := p
  rw [wDiff_single]
  show wDiff data X k (wDiffGen data X (k + 1) n σ) = 0
  rw [wDiffGen, map_add]
  revert σ
  induction n using Fin.cases with
  | zero =>
      intro σ
      have hcs : wDiffW X (k + 1) (0 : Fin (k + 3)) σ
          = (1 + groupRingGen) • Finsupp.single (⟨0, σ⟩ : WSIndex (k + 1) X) 1 :=
        wDiffW_castSucc X (k + 1) 0 σ
      have h1 : wDiff data X k (Finsupp.single (⟨0, σ⟩ : WSIndex (k + 1) X) 1)
          = wDiffGen data X k 0 σ := wDiff_single data X k ⟨0, σ⟩
      rw [hcs, wDiffS_zero, map_zero, add_zero, map_smul, h1, wDiffGen, smul_add,
        smul_wDiffW, wDiffS_zero, smul_zero, add_zero]
  | succ m =>
      induction m using Fin.lastCases with
      | last =>
          intro σ
          have hW : wDiffW X (k + 1) (Fin.succ (Fin.last (k + 1))) σ = 0 :=
            wDiffW_last X (k + 1) σ
          have hz : (fun τ : stdSimplexTop (Fin.last (k + 1)).val ⟶ X =>
              wDiffW X k (Fin.last (k + 1)) τ) = fun _ => (0 : WTensorSMod X k) :=
            funext (wDiffW_last X k)
          rw [hW, map_zero, zero_add, wDiffS_succ, wDiff_lmapDomain,
            linearCombination_wDiffS_bd, add_zero, hz, linearCombination_zero_fun]
      | cast i =>
          intro σ
          have hcs : wDiffW X (k + 1) (Fin.succ (Fin.castSucc i)) σ
              = (1 + groupRingGen) • Finsupp.single (⟨Fin.succ i, σ⟩ : WSIndex (k + 1) X) 1 :=
            wDiffW_castSucc X (k + 1) (Fin.succ i) σ
          have h1 : wDiff data X k (Finsupp.single (⟨Fin.succ i, σ⟩ : WSIndex (k + 1) X) 1)
              = wDiffGen data X k (Fin.succ i) σ := wDiff_single data X k ⟨Fin.succ i, σ⟩
          have hS : wDiff data X k (wDiffS data X (k + 1) (Fin.succ (Fin.castSucc i)) σ)
              = Finsupp.linearCombination GroupRingZ2
                  (fun τ => wDiffW X k (Fin.castSucc i) τ)
                  (data.bd X i.val (Finsupp.single σ (1 : GroupRingZ2))) := by
            rw [wDiffS_succ, wDiff_lmapDomain, linearCombination_wDiffS_bd, add_zero]
            rfl
          rw [hcs, map_smul, h1, wDiffGen, smul_add, smul_wDiffW, zero_add, hS,
            ← mixed_terms_eq]
          exact two_smul_eq_zero _

end

end GroupApproximation.CharClass
