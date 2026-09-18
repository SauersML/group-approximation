import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroNK2Cone
import GroupApproximation.Meta.AxiomGuard

/-!
# Ring maps for the slice reduction of the `NK₂` cone residual

Lane `bh-met-90o`, helper module (ring-generic, no hypothesis).

* `nk2Core_sliceRetract A n : A[s_0..s_n] → A[s_0..s_{n-1}]`, `s_l ↦ s_l` (`l < n`), `s_n ↦ 1`.
  Read on the base `B = A[s_1..s_{n+1}]` of `ψ_{n+1} = finSuccEquiv A (n + 1)`, it is the
  substitution `s_{n+1} ↦ 1` of the cone variable (shifted down by one).
* `nk2Core_sliceRetract_comp_cone`: `ε[t] ∘ ψ_{n+1} ∘ j = ψ_n`, where `j` is the cone
  `s_0 ↦ s_0 s_{n+1}` (`czCubeResFieldCone`).  Checked on constants, on `s_0`
  (`t · C(s_{n+1}) ↦ t`) and on `s_{i+1}` (`C(s_{i+1}) ↦ C(s_{i+1})`).
* `nk2Core_mapMap_comp_shift`, `nk2Core_mapMap_comp_C`: a base change `f : B → B'` commutes with
  `σ_a : t ↦ t + a y` (becoming `σ_{f a}`) and with `C`.
* `nk2Core_K2Map_quillenDiff`: hence `f[t][y] (v_a(u)) = v_{f a}(f[t] u)` in `K₂`.

The identity `ε[t] ∘ ψ_{n+1} ∘ j = ψ_n` and the naturality of `σ_a` were also checked in
`sympy` on random integer polynomials (`n = 3`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

section Slice

variable {A : Type*} [CommRing A]

variable (A) in
/-- The slice retraction `s_l ↦ s_l` (`l < n`), `s_n ↦ 1`, from `A[s_0..s_n]` to
`A[s_0..s_{n-1}]`. -/
noncomputable def nk2Core_sliceRetract (n : ℕ) :
    MvPolynomial (Fin (n + 1)) A →+* MvPolynomial (Fin n) A :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun l ↦
    if h : (l : ℕ) < n then MvPolynomial.X (⟨(l : ℕ), h⟩ : Fin n) else 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_sliceRetract

theorem nk2Core_sliceRetract_C {n : ℕ} (r : A) :
    nk2Core_sliceRetract A n (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.eval₂Hom_C _ _ r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_sliceRetract_C

theorem nk2Core_sliceRetract_X {n : ℕ} (l : Fin (n + 1)) :
    nk2Core_sliceRetract A n (MvPolynomial.X l) =
      if h : (l : ℕ) < n then MvPolynomial.X (⟨(l : ℕ), h⟩ : Fin n) else 1 :=
  MvPolynomial.eval₂Hom_X' _ _ l

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_sliceRetract_X

theorem nk2Core_sliceRetract_X_castSucc {n : ℕ} (i : Fin n) :
    nk2Core_sliceRetract A n (MvPolynomial.X (Fin.castSucc i)) = MvPolynomial.X i := by
  rw [nk2Core_sliceRetract_X]
  exact dif_pos (show ((Fin.castSucc i : Fin (n + 1)) : ℕ) < n from i.isLt)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_sliceRetract_X_castSucc

theorem nk2Core_sliceRetract_X_last {n : ℕ} :
    nk2Core_sliceRetract A n (MvPolynomial.X (Fin.last n)) = 1 := by
  rw [nk2Core_sliceRetract_X]
  exact dif_neg (show ¬((Fin.last n : Fin (n + 1)) : ℕ) < n from Nat.lt_irrefl _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_sliceRetract_X_last

/-- `ψ_k (C r) = C (C r)`. -/
theorem nk2Core_finSuccEquiv_C (k : ℕ) (r : A) :
    MvPolynomial.finSuccEquiv A k (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_finSuccEquiv_C

variable (A) in
/-- `ε[t] ∘ ψ_{n+1} ∘ j = ψ_n`: slicing the cone variable at `1` undoes the cone. -/
theorem nk2Core_sliceRetract_comp_cone (n : ℕ) :
    (Polynomial.mapRingHom (nk2Core_sliceRetract A n)).comp
        ((MvPolynomial.finSuccEquiv A (n + 1)).toRingEquiv.toRingHom.comp
          (czCubeResFieldCone A n)) =
      (MvPolynomial.finSuccEquiv A n).toRingEquiv.toRingHom := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun l ↦ ?_)
  · show Polynomial.map (nk2Core_sliceRetract A n)
        (MvPolynomial.finSuccEquiv A (n + 1) (czCubeResFieldCone A n (MvPolynomial.C r))) =
      MvPolynomial.finSuccEquiv A n (MvPolynomial.C r)
    rw [czCubeResFieldCone_C, nk2Core_finSuccEquiv_C, nk2Core_finSuccEquiv_C, Polynomial.map_C,
      nk2Core_sliceRetract_C]
  · show Polynomial.map (nk2Core_sliceRetract A n)
        (MvPolynomial.finSuccEquiv A (n + 1) (czCubeResFieldCone A n (MvPolynomial.X l))) =
      MvPolynomial.finSuccEquiv A n (MvPolynomial.X l)
    rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨i, rfl⟩
    · rw [czCubeResFieldCone_X_zero, map_mul, Fin.castSucc_zero, ← Fin.succ_last n,
        MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_zero,
        MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
        nk2Core_sliceRetract_X_last, map_one, mul_one]
    · rw [czCubeResFieldCone_X_of_ne (Fin.succ_ne_zero i), ← Fin.succ_castSucc,
        MvPolynomial.finSuccEquiv_X_succ, MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C,
        nk2Core_sliceRetract_X_castSucc]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_sliceRetract_comp_cone

end Slice
