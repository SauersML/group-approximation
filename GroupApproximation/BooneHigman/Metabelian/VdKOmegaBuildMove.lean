import GroupApproximation.BooneHigman.Metabelian.VdKOmegaGen
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Building `Ω`, part 1: moving the mixed relation from one index pair to all of them

Lane `bh-met-92v`.  Fix a group `G`, homomorphisms `α : P̃ →* G` and `β : P̃⁻ →* G` out of the
column and row parabolics, and assume they agree on `St_n(R)` (`vdkOmega_Agree`).

Write `vdkOmegaBuild_Full α β i k` for the family of mixed relations at the index pair `(i, k)`:
`⁅x_{i,last}(a), x_{last,k}(b)⁆ = x_{ik}(ab)` for all `a b`.  So `vdkOmega_Mixed α β` is
definitionally `∀ i k, vdkOmegaBuild_Full α β i k`.

This file proves two moves, using only the semidirect-product relators of
`VdKOmegaGen.lean` and the Steinberg relators of `St_n(R)`:

* `vdkOmegaBuild_moveSnd`: the single identity at `(i, j)` with `b = 1` gives the relation at
  `(i, k, a, b)` for any third index `k`;
* `vdkOmegaBuild_moveFst`: the single identity at `(j, k)` with `a = 1` gives the relation at
  `(i, k, a, b)` for any third index `i`.

Both rest on two identities that hold in any group, `vdkOmegaBuild_comm_step` and
`vdkOmegaBuild_comm_step'`.  They were falsification-searched in `S_6` and every instance was
checked in `SL_4(Z/5)` (scratchpad `bh-met-92v/check.py`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

variable {n : ℕ} {R : Type*} [CommRing R] {G : Type*} [Group G]

/-- Group identity A.  If `Z` commutes with `X`, `⁅X, Y⁆ = W`, `⁅W, Z⁆ = T`, and both `W` and
`T` commute with `⁅Y, Z⁆`, then `⁅X, ⁅Y, Z⁆⁆ = T`. -/
theorem vdkOmegaBuild_comm_step {X Y Z W T : G} (hZX : Z * X * Z⁻¹ = X) (hXY : ⁅X, Y⁆ = W)
    (hWV : W * ⁅Y, Z⁆ * W⁻¹ = ⁅Y, Z⁆) (hWZ : ⁅W, Z⁆ = T)
    (hTV : T * ⁅Y, Z⁆ * T⁻¹ = ⁅Y, Z⁆) : ⁅X, ⁅Y, Z⁆⁆ = T := by
  have hc0 : Commute Z X := mul_inv_eq_iff_eq_mul.mp hZX
  have hXZ : X * Z * X⁻¹ = Z := by rw [← hc0.eq, mul_inv_cancel_right]
  have hXY' : X * Y * X⁻¹ = W * Y := by
    rw [← hXY]
    group
  have hconj : X * ⁅Y, Z⁆ * X⁻¹ = ⁅W * Y, Z⁆ := by
    calc X * ⁅Y, Z⁆ * X⁻¹ = ⁅X * Y * X⁻¹, X * Z * X⁻¹⁆ := by group
      _ = ⁅W * Y, Z⁆ := by rw [hXY', hXZ]
  have hsplit : ⁅W * Y, Z⁆ = W * ⁅Y, Z⁆ * W⁻¹ * ⁅W, Z⁆ := by group
  have hc : Commute T ⁅Y, Z⁆ := mul_inv_eq_iff_eq_mul.mp hTV
  calc ⁅X, ⁅Y, Z⁆⁆ = X * ⁅Y, Z⁆ * X⁻¹ * ⁅Y, Z⁆⁻¹ := commutatorElement_def _ _
    _ = ⁅Y, Z⁆ * T * ⁅Y, Z⁆⁻¹ := by rw [hconj, hsplit, hWV, hWZ]
    _ = T := by rw [← hc.eq, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_comm_step

/-- Group identity B.  If `Y` commutes with `V`, `⁅Z, V⁆ = W`, `⁅Y, W⁆ = T`, `W` commutes with
`⁅Y, Z⁆` and `T` commutes with `W`, then `⁅⁅Y, Z⁆, V⁆ = T`. -/
theorem vdkOmegaBuild_comm_step' {Y Z V W T : G} (hYV : Y * V * Y⁻¹ = V) (hZV : ⁅Z, V⁆ = W)
    (hYW : ⁅Y, W⁆ = T) (hWX : W * ⁅Y, Z⁆ * W⁻¹ = ⁅Y, Z⁆) (hTW : Commute T W) :
    ⁅⁅Y, Z⁆, V⁆ = T := by
  have hc1 : Commute Y V := mul_inv_eq_iff_eq_mul.mp hYV
  have hVY : V * Y * V⁻¹ = Y := by rw [← hc1.eq, mul_inv_cancel_right]
  have hVZ : V * Z * V⁻¹ = W⁻¹ * Z := by
    rw [← hZV]
    group
  have hconj : V * ⁅Y, Z⁆ * V⁻¹ = ⁅Y, W⁻¹ * Z⁆ := by
    calc V * ⁅Y, Z⁆ * V⁻¹ = ⁅V * Y * V⁻¹, V * Z * V⁻¹⁆ := by group
      _ = ⁅Y, W⁻¹ * Z⁆ := by rw [hVY, hVZ]
  have hsplit : ⁅Y, W⁻¹ * Z⁆ = W⁻¹ * ⁅Y, W⁆⁻¹ * W * (W⁻¹ * ⁅Y, Z⁆ * W) := by group
  have hc2 : Commute W ⁅Y, Z⁆ := mul_inv_eq_iff_eq_mul.mp hWX
  have hWX' : W⁻¹ * ⁅Y, Z⁆ * W = ⁅Y, Z⁆ := by
    rw [mul_assoc, ← hc2.eq, inv_mul_cancel_left]
  have hTW' : W⁻¹ * T⁻¹ * W = T⁻¹ := by
    rw [mul_assoc, hTW.inv_left.eq, inv_mul_cancel_left]
  calc ⁅⁅Y, Z⁆, V⁆ = ⁅Y, Z⁆ * (V * ⁅Y, Z⁆ * V⁻¹)⁻¹ := by group
    _ = ⁅Y, Z⁆ * (W⁻¹ * ⁅Y, W⁆⁻¹ * W * (W⁻¹ * ⁅Y, Z⁆ * W))⁻¹ := by rw [hconj, hsplit]
    _ = ⁅Y, Z⁆ * (T⁻¹ * ⁅Y, Z⁆)⁻¹ := by rw [hWX', hYW, hTW']
    _ = T := by group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_comm_step'

variable (α : vdkParPres_Tilde n R →* G) (β : vdkOmega_TildeMinus n R →* G)

/-- Moving the second index: the single identity `⁅x_{i,last}(a), x_{last,j}(1)⁆ = x_{ij}(a)`
gives `⁅x_{i,last}(a), x_{last,k}(b)⁆ = x_{ik}(ab)` for every `k ∉ {i, j}` and every `b`. -/
theorem vdkOmegaBuild_moveSnd (hαβ : vdkOmega_Agree α β) (i j k : Fin n) (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) (a b : R)
    (h : ⁅vdkOmega_cv α (Pi.single i a), vdkOmega_rv β (Pi.single j 1)⁆ =
      α (vdkParPres_inr (x i j hij a))) :
    ⁅vdkOmega_cv α (Pi.single i a), vdkOmega_rv β (Pi.single k b)⁆ =
      α (vdkParPres_inr (x i k hik (a * b))) := by
  have hV : vdkOmega_rv β (Pi.single k b) =
      ⁅vdkOmega_rv β (Pi.single j 1), α (vdkParPres_inr (x j k hjk b))⁆ := by
    rw [vdkOmega_rv_sv_adj α β hαβ j k hjk 1 b, one_mul]
  rw [hV]
  refine vdkOmegaBuild_comm_step ?_ h ?_ ?_ ?_
  · exact vdkOmega_conj_cv_triv α j k hjk b i a hik.symm
  · rw [← hV]
    exact vdkOmega_conj_rv_triv α β hαβ i j hij a k b hik
  · rw [vdkOmega_inr_commutator, x_commutator i j k hij hjk hik a b]
  · rw [← hV]
    exact vdkOmega_conj_rv_triv α β hαβ i k hik (a * b) k b hik

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_moveSnd

/-- Moving the first index: the single identity `⁅x_{j,last}(1), x_{last,k}(b)⁆ = x_{jk}(b)`
gives `⁅x_{i,last}(a), x_{last,k}(b)⁆ = x_{ik}(ab)` for every `i ∉ {j, k}` and every `a`. -/
theorem vdkOmegaBuild_moveFst (hαβ : vdkOmega_Agree α β) (i j k : Fin n) (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) (a b : R)
    (h : ⁅vdkOmega_cv α (Pi.single j 1), vdkOmega_rv β (Pi.single k b)⁆ =
      α (vdkParPres_inr (x j k hjk b))) :
    ⁅vdkOmega_cv α (Pi.single i a), vdkOmega_rv β (Pi.single k b)⁆ =
      α (vdkParPres_inr (x i k hik (a * b))) := by
  have hX : vdkOmega_cv α (Pi.single i a) =
      ⁅α (vdkParPres_inr (x i j hij a)), vdkOmega_cv α (Pi.single j 1)⁆ := by
    rw [vdkOmega_sv_cv_adj α i j hij a 1, mul_one]
  rw [hX]
  refine vdkOmegaBuild_comm_step' ?_ h ?_ ?_ ?_
  · exact vdkOmega_conj_rv_triv α β hαβ i j hij a k b hik
  · rw [vdkOmega_inr_commutator, x_commutator i j k hij hjk hik a b]
  · rw [← hX]
    exact vdkOmega_conj_cv_triv α j k hjk b i a hik.symm
  · exact ((x_commute_of_ne i k j k hik hjk hjk.symm hik.symm (a * b) b).map
      vdkParPres_inr).map α

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaBuild_moveFst

end GroupApproximation.BooneHigman.Metabelian.ElemFP
