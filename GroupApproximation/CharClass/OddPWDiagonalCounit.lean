import GroupApproximation.CharClass.OddPWDiagonal

/-!
# `ψ_W` is counital

`notes/lix-stronger-lane-reports/sp-steenrod.md` §6.2.  The augmentation `ε : W → F_p` sends every
`T^u e_0` to `1` and kills positive degrees, and the counit laws are

```text
(ε ⊗ 1) ψ = id ,     (1 ⊗ ε) ψ = id .
```

In bidegree `(a, b)` the map `ε ⊗ 1` keeps `a = 0` only and pushes `F_p[ℤ/p × ℤ/p]` forward along
the second projection; `1 ⊗ ε` keeps `b = 0` and pushes along the first.  Only one term of `ψ(x)`
survives each: `(0, n)`, whose coefficient is `φ(0, n) = 1`, and `(n, 0)`, whose coefficient is `1`
or `T₂`, and `T₂` goes to `1` under the first projection.  Each projection undoes the diagonal.

## Main results

* `psiW_counitLeft`  — `(ε ⊗ 1) ψ_n = id`.
* `psiW_counitRight` — `(1 ⊗ ε) ψ_n = id`.
-/

namespace GroupApproximation.CharClass

open Finset

noncomputable section

/-- A basis vector `T^u e_a` of `W`, as `(a, u)`. -/
abbrev WIdx (p : ℕ) : Type := ℕ × ZMod p

/-- `W` as a free `F_p`-module, all degrees at once. -/
abbrev WAll (p : ℕ) : Type := WIdx p →₀ ZMod p

/-- The degree-`n` summand `W_n = Λ`, placed in `W`. -/
def wdEmb (p n : ℕ) : GroupRingZMod p →ₗ[ZMod p] WAll p :=
  Finsupp.lmapDomain (ZMod p) (ZMod p)
      (fun g : Multiplicative (ZMod p) => ((n, Multiplicative.toAdd g) : WIdx p)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv (ZMod p)).toLinearMap

/-- `ε ⊗ 1 : W ⊗ W → W`. -/
def wwCounitLeft (p : ℕ) : WWAll p →ₗ[ZMod p] WAll p :=
  Finsupp.linearCombination (ZMod p) fun i : WWIdx p =>
    if i.1 = 0 then Finsupp.single ((i.2.2.1, i.2.2.2) : WIdx p) (1 : ZMod p) else 0

/-- `1 ⊗ ε : W ⊗ W → W`. -/
def wwCounitRight (p : ℕ) : WWAll p →ₗ[ZMod p] WAll p :=
  Finsupp.linearCombination (ZMod p) fun i : WWIdx p =>
    if i.2.2.1 = 0 then Finsupp.single ((i.1, i.2.1) : WIdx p) (1 : ZMod p) else 0

/-- Push forward along the second projection. -/
def wdPushSnd (p : ℕ) : GroupRingZMod2 p →ₐ[ZMod p] GroupRingZMod p :=
  MonoidAlgebra.mapDomainAlgHom (ZMod p) (ZMod p)
    (MonoidHom.snd (Multiplicative (ZMod p)) (Multiplicative (ZMod p)))

/-- Push forward along the first projection. -/
def wdPushFst (p : ℕ) : GroupRingZMod2 p →ₐ[ZMod p] GroupRingZMod p :=
  MonoidAlgebra.mapDomainAlgHom (ZMod p) (ZMod p)
    (MonoidHom.fst (Multiplicative (ZMod p)) (Multiplicative (ZMod p)))

theorem wdPushSnd_wdDiag (p : ℕ) (x : GroupRingZMod p) : wdPushSnd p (wdDiag p x) = x := by
  induction x using MonoidAlgebra.induction_on with
  | hM g => simp [wdDiag_single, wdPushSnd, MonoidAlgebra.mapDomain_single]
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hsmul c x hx => simp only [map_smul, hx]

theorem wdPushFst_wdDiag (p : ℕ) (x : GroupRingZMod p) : wdPushFst p (wdDiag p x) = x := by
  induction x using MonoidAlgebra.induction_on with
  | hM g => simp [wdDiag_single, wdPushFst, MonoidAlgebra.mapDomain_single]
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hsmul c x hx => simp only [map_smul, hx]

theorem wdPushFst_wdT2 (p : ℕ) : wdPushFst p (wdT2 p) = 1 := by
  simp [wdPushFst, wdT2, MonoidAlgebra.mapDomain_single, MonoidAlgebra.one_def]

theorem wwCounitLeft_atBideg (p a b : ℕ) (r : GroupRingZMod2 p) :
    wwCounitLeft p (wdAtBideg p a b r) = if a = 0 then wdEmb p b (wdPushSnd p r) else 0 := by
  induction r using MonoidAlgebra.induction_on with
  | hM g =>
      rw [MonoidAlgebra.of_apply, wdAtBideg_single, wwCounitLeft, Finsupp.linearCombination_single,
        one_smul]
      by_cases h : a = 0
      · simp [h, wdEmb, wdPushSnd, MonoidAlgebra.mapDomain_single, Finsupp.mapDomain_single]
      · simp [h]
  | hadd x y hx hy =>
      simp only [map_add, hx, hy]
      split_ifs <;> simp
  | hsmul c x hx =>
      simp only [map_smul, hx]
      split_ifs <;> simp

theorem wwCounitRight_atBideg (p a b : ℕ) (r : GroupRingZMod2 p) :
    wwCounitRight p (wdAtBideg p a b r) = if b = 0 then wdEmb p a (wdPushFst p r) else 0 := by
  induction r using MonoidAlgebra.induction_on with
  | hM g =>
      rw [MonoidAlgebra.of_apply, wdAtBideg_single, wwCounitRight,
        Finsupp.linearCombination_single, one_smul]
      by_cases h : b = 0
      · simp [h, wdEmb, wdPushFst, MonoidAlgebra.mapDomain_single, Finsupp.mapDomain_single]
      · simp [h]
  | hadd x y hx hy =>
      simp only [map_add, hx, hy]
      split_ifs <;> simp
  | hsmul c x hx =>
      simp only [map_smul, hx]
      split_ifs <;> simp

theorem wdPhiG_zero_left (p b : ℕ) : wdPhiG p 0 b = 1 := by
  simp [wdPhiG, wdPhi]

theorem wdPushFst_wdPhiG_right (p a : ℕ) : wdPushFst p (wdPhiG p a 0) = 1 := by
  by_cases ha : Even a
  · simp [wdPhiG, wdPhi, ha]
  · simp [wdPhiG, wdPhi, ha, wdPushFst_wdT2]

/-- **`(ε ⊗ 1) ψ_n = id`.** -/
theorem psiW_counitLeft (p n : ℕ) (x : GroupRingZMod p) :
    wwCounitLeft p (psiW p n x) = wdEmb p n x := by
  rw [psiW_apply, map_sum]
  simp only [wwCounitLeft_atBideg]
  cases n with
  | zero => simp [wdPhiG_zero_left, wdPushSnd_wdDiag]
  | succ m =>
      rw [Finset.Nat.sum_antidiagonal_succ]
      simp [wdPhiG_zero_left, wdPushSnd_wdDiag]

/-- **`(1 ⊗ ε) ψ_n = id`.** -/
theorem psiW_counitRight (p n : ℕ) (x : GroupRingZMod p) :
    wwCounitRight p (psiW p n x) = wdEmb p n x := by
  rw [psiW_apply, map_sum]
  simp only [wwCounitRight_atBideg]
  cases n with
  | zero => simp [wdPushFst_wdDiag, wdPushFst_wdPhiG_right]
  | succ m =>
      rw [Finset.Nat.sum_antidiagonal_succ']
      simp [wdPushFst_wdDiag, wdPushFst_wdPhiG_right]

end

end GroupApproximation.CharClass

open GroupApproximation.CharClass

#audit_axioms psiW_counitLeft
#audit_axioms psiW_counitRight
