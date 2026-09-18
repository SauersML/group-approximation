import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeNilFieldPos
import GroupApproximation.Meta.AxiomGuard

/-!
# The general cone substitution `R[s_0..s_n] → R[s_0..s_{n+1}]`, `s_0 ↦ s_0 s_{n+1}`

Lane `bh-met-81`, helper module (ring-generic, no hypothesis).  Module
`ElemFPK2CubeNilFieldCone` has the cone `s_0 ↦ s_0 s_1` for one variable only.  Here, for any
commutative ring `R` and any `n`, write `j = czCubeResFieldCone R n`:
`s_0 ↦ s_0 s_{n+1}` and `s_i ↦ s_i` for `1 ≤ i ≤ n`, and `r = czCubeResFieldConeRetract R n`:
`s_l ↦ s_l` for `l ≤ n` and `s_{n+1} ↦ 1`.

* `czCubeResField_retract_comp_cone`: `r ∘ j = id`.
* `czCubeResField_cubeKill_castSucc_comp_cone`: `π_i ∘ j = j ∘ π_i` for `i ≤ n`.
* `czCubeResField_cubeKill_last_comp_cone`: `π_{n+1} ∘ j = j ∘ π_0`, since `π_{n+1}(s_0 s_{n+1}) = 0`.
* `czCubeResField_K2Map_cubeKill_cone`: if `u ∈ K₂(N, R[s_0..s_n])` is killed by every `π_i`,
  then `j u` is killed by every `π_i`, `i ≤ n + 1`.
* `czCubeResField_dies_of_cone_step`: if every element of `K₂(N, R[s_0..s_{n+1}])` killed by every
  `π_i` dies after padding, so does every such element of `K₂(N, R[s_0..s_n])` (apply `r`).
* `czCubeResField_dies_of_cone_iter`: iterating, the cube form with `n + r + 1` variables at a
  fixed rank `N` gives the cube form with `n + 1` variables at the same rank `N`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

section Cone

variable {R : Type*} [CommRing R]

variable (R) in
/-- The cone substitution `s_0 ↦ s_0 s_{n+1}`, `s_i ↦ s_i` (`1 ≤ i ≤ n`), from `R[s_0..s_n]` to
`R[s_0..s_{n+1}]`. -/
noncomputable def czCubeResFieldCone (n : ℕ) :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin (n + 1 + 1)) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun i ↦
    if i = 0 then MvPolynomial.X (Fin.castSucc i) * MvPolynomial.X (Fin.last (n + 1))
    else MvPolynomial.X (Fin.castSucc i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldCone

variable (R) in
/-- The retraction `s_l ↦ s_l` (`l ≤ n`), `s_{n+1} ↦ 1`, from `R[s_0..s_{n+1}]` to
`R[s_0..s_n]`. -/
noncomputable def czCubeResFieldConeRetract (n : ℕ) :
    MvPolynomial (Fin (n + 1 + 1)) R →+* MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun l ↦
    if h : (l : ℕ) < n + 1 then MvPolynomial.X (⟨(l : ℕ), h⟩ : Fin (n + 1)) else 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldConeRetract

theorem czCubeResFieldCone_C {n : ℕ} (r : R) :
    czCubeResFieldCone R n (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.eval₂Hom_C _ _ r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldCone_C

theorem czCubeResFieldCone_X {n : ℕ} (i : Fin (n + 1)) :
    czCubeResFieldCone R n (MvPolynomial.X i) =
      if i = 0 then MvPolynomial.X (Fin.castSucc i) * MvPolynomial.X (Fin.last (n + 1))
      else MvPolynomial.X (Fin.castSucc i) :=
  MvPolynomial.eval₂Hom_X' _ _ i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldCone_X

theorem czCubeResFieldCone_X_zero {n : ℕ} :
    czCubeResFieldCone R n (MvPolynomial.X 0) =
      MvPolynomial.X (Fin.castSucc 0) * MvPolynomial.X (Fin.last (n + 1)) :=
  (czCubeResFieldCone_X (0 : Fin (n + 1))).trans (if_pos rfl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldCone_X_zero

theorem czCubeResFieldCone_X_of_ne {n : ℕ} {i : Fin (n + 1)} (h : i ≠ 0) :
    czCubeResFieldCone R n (MvPolynomial.X i) = MvPolynomial.X (Fin.castSucc i) :=
  (czCubeResFieldCone_X i).trans (if_neg h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldCone_X_of_ne

theorem czCubeResFieldConeRetract_C {n : ℕ} (r : R) :
    czCubeResFieldConeRetract R n (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.eval₂Hom_C _ _ r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldConeRetract_C

theorem czCubeResFieldConeRetract_X {n : ℕ} (l : Fin (n + 1 + 1)) :
    czCubeResFieldConeRetract R n (MvPolynomial.X l) =
      if h : (l : ℕ) < n + 1 then MvPolynomial.X (⟨(l : ℕ), h⟩ : Fin (n + 1)) else 1 :=
  MvPolynomial.eval₂Hom_X' _ _ l

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldConeRetract_X

theorem czCubeResFieldConeRetract_X_castSucc {n : ℕ} (i : Fin (n + 1)) :
    czCubeResFieldConeRetract R n (MvPolynomial.X (Fin.castSucc i)) = MvPolynomial.X i := by
  rw [czCubeResFieldConeRetract_X]
  exact dif_pos (show ((Fin.castSucc i : Fin (n + 1 + 1)) : ℕ) < n + 1 from i.is_lt)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldConeRetract_X_castSucc

theorem czCubeResFieldConeRetract_X_last {n : ℕ} :
    czCubeResFieldConeRetract R n (MvPolynomial.X (Fin.last (n + 1))) = 1 := by
  rw [czCubeResFieldConeRetract_X]
  exact dif_neg (show ¬((Fin.last (n + 1) : Fin (n + 1 + 1)) : ℕ) < n + 1 from Nat.lt_irrefl _)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeResFieldConeRetract_X_last
