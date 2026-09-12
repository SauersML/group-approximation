import GroupApproximation.CharClass.OddPWDiagonalRing
import GroupApproximation.CharClass.OddPResolution
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Algebra.Bilinear

/-!
# The resolution coproduct `ψ_W : W → W ⊗_{F_p} W`

`notes/lix-stronger-lane-reports/sp-steenrod.md` §6.2.  The Cartan comparison `B` needs a chain map
`ψ : W → W ⊗ W`, `Λ`-linear for the diagonal action and counital, where `W = Wodd p` is the periodic
resolution over `Λ = F_p[ℤ/p]`.

## The carrier

`W ⊗_{F_p} W` is the free `F_p`-module on `(a, u, b, v)`, the basis vector `T^u e_a ⊗ T^v e_b`
(`WWAll p`, all bidegrees at once).  Its differential is

```text
d(T^u e_a ⊗ T^v e_b) = d(T^u e_a) ⊗ T^v e_b + (−1)^a T^u e_a ⊗ d(T^v e_b),
d e_{k+1} = altCoeff (grS p) (grNorm p) k · e_k     (T − 1 into even k, N into odd k).
```

One bidegree `(a, b)` is a copy of the group ring of `ℤ/p × ℤ/p` (`GroupRingZMod2 p`), with `T₁` on
the left factor and `T₂` on the right, placed by `wdAtBideg p a b`.  `wwDAll_atBideg` says what the
differential does to a whole bidegree at once: multiplication by `c_a(T₁)` into `(a−1, b)` and by
`(−1)^a c_b(T₂)` into `(a, b−1)`.  That is what reduces the chain-map condition to the ring identity
`wdChain_identity` of `CharClass/OddPWDiagonalRing.lean`.

## The coproduct

`psiW p n x = Σ_{a+b=n} wdAtBideg a b (Δx · φ(a, b))`, with `Δ : Λ → F_p[ℤ/p × ℤ/p]` the diagonal
`T ↦ T₁T₂` and `φ(a, b) ∈ {1, T₂, Q}` the closed form of `sp-design`.  On `x = 1` it is the closed
form; `Λ`-linearity is built in, because `x` enters through `Δ`.

## Main results

* `psiW_chainMap` — **`ψ ∘ d = d ∘ ψ`**, in every degree.
* `psiW_grGen_mul` — **`Λ`-linearity for the diagonal action**: `ψ(T x) = (T ⊗ T) ψ(x)`.
* `psiW_one` — the closed form on the generator `e_n`.
-/

namespace GroupApproximation.CharClass

open Finset

noncomputable section

/-! ## 1. The carrier and one bidegree -/

/-- A basis vector `T^u e_a ⊗ T^v e_b` of `W ⊗_{F_p} W`, as `(a, u, b, v)`. -/
abbrev WWIdx (p : ℕ) : Type := ℕ × ZMod p × ℕ × ZMod p

/-- **`W ⊗_{F_p} W`**, the free `F_p`-module on `WWIdx p`, all bidegrees at once. -/
abbrev WWAll (p : ℕ) : Type := WWIdx p →₀ ZMod p

/-- The group ring of `ℤ/p × ℤ/p`: one bidegree of `W ⊗ W`. -/
abbrev GroupRingZMod2 (p : ℕ) : Type :=
  MonoidAlgebra (ZMod p) (Multiplicative (ZMod p) × Multiplicative (ZMod p))

/-- `T₁`, the generator acting on the left factor. -/
def wdT1 (p : ℕ) : GroupRingZMod2 p :=
  MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod p), 1) 1

/-- `T₂`, the generator acting on the right factor. -/
def wdT2 (p : ℕ) : GroupRingZMod2 p :=
  MonoidAlgebra.single (1, Multiplicative.ofAdd (1 : ZMod p)) 1

theorem wdT2_pow_card (p : ℕ) : wdT2 p ^ p = 1 := by
  unfold wdT2
  rw [MonoidAlgebra.single_pow, one_pow, MonoidAlgebra.one_def]
  congr 1
  refine Prod.ext ?_ ?_
  · show (1 : Multiplicative (ZMod p)) ^ p = 1
    exact one_pow p
  · show (Multiplicative.ofAdd (1 : ZMod p)) ^ p = 1
    rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, ofAdd_zero]

/-- The diagonal `Λ → F_p[ℤ/p × ℤ/p]`, `T ↦ T₁T₂`. -/
def wdDiag (p : ℕ) : GroupRingZMod p →ₐ[ZMod p] GroupRingZMod2 p :=
  MonoidAlgebra.mapDomainAlgHom (ZMod p) (ZMod p)
    ((MonoidHom.id (Multiplicative (ZMod p))).prod (MonoidHom.id (Multiplicative (ZMod p))))

theorem wdDiag_single (p : ℕ) (g : Multiplicative (ZMod p)) (c : ZMod p) :
    wdDiag p (MonoidAlgebra.single g c) = MonoidAlgebra.single (g, g) c := by
  simp [wdDiag, MonoidAlgebra.mapDomain_single]

theorem wdDiag_grGen (p : ℕ) : wdDiag p (grGen p) = wdT1 p * wdT2 p := by
  unfold grGen
  rw [wdDiag_single, wdT1, wdT2, MonoidAlgebra.single_mul_single]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]

/-- The diagonal carries the differential coefficient of `Wodd` to `c_n(T₁T₂)`. -/
theorem wdDiag_altCoeff (p n : ℕ) :
    wdDiag p (altCoeff (grS p) (grNorm p) n) = wdCAlt p n (wdT1 p * wdT2 p) := by
  unfold altCoeff wdCAlt
  split_ifs
  · rw [grS, map_sub, map_one, wdDiag_grGen]
  · simp only [grNorm, map_sum, map_pow, wdDiag_grGen, wdNormSum]

/-- **The bidegree `(a, b)` of `W ⊗ W`**: `T₁^u T₂^v ↦ T^u e_a ⊗ T^v e_b`. -/
def wdAtBideg (p a b : ℕ) : GroupRingZMod2 p →ₗ[ZMod p] WWAll p :=
  Finsupp.lmapDomain (ZMod p) (ZMod p)
      (fun g : Multiplicative (ZMod p) × Multiplicative (ZMod p) =>
        ((a, Multiplicative.toAdd g.1, b, Multiplicative.toAdd g.2) : WWIdx p)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv (ZMod p)).toLinearMap

theorem wdAtBideg_single (p a b : ℕ) (g : Multiplicative (ZMod p) × Multiplicative (ZMod p))
    (c : ZMod p) :
    wdAtBideg p a b (MonoidAlgebra.single g c)
      = Finsupp.single ((a, Multiplicative.toAdd g.1, b, Multiplicative.toAdd g.2) : WWIdx p) c := by
  simp [wdAtBideg, Finsupp.mapDomain_single]

/-! ## 2. The differential -/

/-- The left half of the differential on one bidegree: `c_{a-1}(T₁)` into `(a − 1, b)`. -/
def wdLeftBd (p : ℕ) : ℕ → ℕ → GroupRingZMod2 p →ₗ[ZMod p] WWAll p
  | 0, _ => 0
  | a + 1, b => wdAtBideg p a b ∘ₗ LinearMap.mulLeft (ZMod p) (wdCAlt p a (wdT1 p))

/-- The right half of the differential on one bidegree: `(−1)^a c_{b-1}(T₂)` into `(a, b − 1)`. -/
def wdRightBd (p : ℕ) : ℕ → ℕ → GroupRingZMod2 p →ₗ[ZMod p] WWAll p
  | _, 0 => 0
  | a, b + 1 =>
      ((-1 : ZMod p) ^ a) • (wdAtBideg p a b ∘ₗ LinearMap.mulLeft (ZMod p) (wdCAlt p b (wdT2 p)))

theorem wdLeftBd_zero (p b : ℕ) (r : GroupRingZMod2 p) : wdLeftBd p 0 b r = 0 := rfl

theorem wdLeftBd_succ (p a b : ℕ) (r : GroupRingZMod2 p) :
    wdLeftBd p (a + 1) b r = wdAtBideg p a b (wdCAlt p a (wdT1 p) * r) := rfl

theorem wdRightBd_zero (p a : ℕ) (r : GroupRingZMod2 p) : wdRightBd p a 0 r = 0 := rfl

theorem wdRightBd_succ (p a b : ℕ) (r : GroupRingZMod2 p) :
    wdRightBd p a (b + 1) r = ((-1 : ZMod p) ^ a) • wdAtBideg p a b (wdCAlt p b (wdT2 p) * r) :=
  rfl

/-- The basis vector `T^u e_a ⊗ T^v e_b` inside its bidegree. -/
def wdMono (p : ℕ) (u v : ZMod p) : GroupRingZMod2 p :=
  MonoidAlgebra.single (Multiplicative.ofAdd u, Multiplicative.ofAdd v) 1

/-- The differential on one basis vector. -/
def wdBdGen (p : ℕ) (i : WWIdx p) : WWAll p :=
  wdLeftBd p i.1 i.2.2.1 (wdMono p i.2.1 i.2.2.2) + wdRightBd p i.1 i.2.2.1 (wdMono p i.2.1 i.2.2.2)

/-- **The differential of `W ⊗_{F_p} W`**: `d(x ⊗ y) = dx ⊗ y + (−1)^a x ⊗ dy`. -/
def wwDAll (p : ℕ) : Module.End (ZMod p) (WWAll p) :=
  Finsupp.linearCombination (ZMod p) (wdBdGen p)

/-- **The differential on a whole bidegree.** -/
theorem wwDAll_atBideg (p a b : ℕ) (r : GroupRingZMod2 p) :
    wwDAll p (wdAtBideg p a b r) = wdLeftBd p a b r + wdRightBd p a b r := by
  induction r using MonoidAlgebra.induction_on with
  | hM g =>
      rw [MonoidAlgebra.of_apply, wdAtBideg_single, wwDAll, Finsupp.linearCombination_single,
        one_smul, wdBdGen]
      simp [wdMono]
  | hadd x y hx hy =>
      simp only [map_add, hx, hy]
      abel
  | hsmul c x hx => simp only [map_smul, hx, smul_add]

/-! ## 3. The coproduct -/

/-- The closed-form coefficient `φ(a, b) ∈ {1, T₂, Q}` in the group ring of `ℤ/p × ℤ/p`. -/
def wdPhiG (p a b : ℕ) : GroupRingZMod2 p := wdPhi p a b (wdT1 p) (wdT2 p)

/-- **The resolution coproduct `ψ_W` in degree `n`**, `F_p`-linear on `W_n = Λ`:
`ψ(x) = Σ_{a+b=n} Δx · φ(a, b)` placed in bidegree `(a, b)`. -/
def psiW (p n : ℕ) : GroupRingZMod p →ₗ[ZMod p] WWAll p :=
  ∑ i ∈ antidiagonal n,
    wdAtBideg p i.1 i.2 ∘ₗ LinearMap.mulRight (ZMod p) (wdPhiG p i.1 i.2) ∘ₗ
      (wdDiag p).toLinearMap

theorem psiW_apply (p n : ℕ) (x : GroupRingZMod p) :
    psiW p n x = ∑ i ∈ antidiagonal n, wdAtBideg p i.1 i.2 (wdDiag p x * wdPhiG p i.1 i.2) := by
  simp only [psiW, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]

/-- **The closed form on the generator `e_n`.** -/
theorem psiW_one (p n : ℕ) :
    psiW p n 1 = ∑ i ∈ antidiagonal n, wdAtBideg p i.1 i.2 (wdPhiG p i.1 i.2) := by
  simp only [psiW_apply, map_one, one_mul]

/-- **`ψ_W` is a chain map**: `ψ(d x) = d(ψ x)` for `x ∈ W_{n+1}`. -/
theorem psiW_chainMap (p n : ℕ) (x : GroupRingZMod p) :
    psiW p n (altCoeff (grS p) (grNorm p) n * x) = wwDAll p (psiW p (n + 1) x) := by
  rw [psiW_apply, psiW_apply, map_sum]
  simp only [wwDAll_atBideg]
  rw [Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.sum_antidiagonal_succ']
  simp only [wdLeftBd_zero, wdRightBd_zero, zero_add, wdLeftBd_succ, wdRightBd_succ]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i.1 + i.2 = n := Finset.mem_antidiagonal.mp hi
  rw [← map_smul, ← map_add]
  congr 1
  have key := wdChain_identity p (T₁ := wdT1 p) (wdT2_pow_card p) i.1 i.2
  rw [map_mul (wdDiag p), ← hi', wdDiag_altCoeff, Algebra.smul_def, map_pow, map_neg, map_one]
  simp only [wdPhiG]
  linear_combination (-wdDiag p x) * key

/-! ## 4. Equivariance for the diagonal action -/

/-- The diagonal action of `T` on `W ⊗ W`: `T^u e_a ⊗ T^v e_b ↦ T^{u+1} e_a ⊗ T^{v+1} e_b`. -/
def wwDiagAct (p : ℕ) : Module.End (ZMod p) (WWAll p) :=
  Finsupp.lmapDomain (ZMod p) (ZMod p)
    (fun i : WWIdx p => ((i.1, 1 + i.2.1, i.2.2.1, 1 + i.2.2.2) : WWIdx p))

theorem wwDiagAct_atBideg (p a b : ℕ) (r : GroupRingZMod2 p) :
    wwDiagAct p (wdAtBideg p a b r) = wdAtBideg p a b (wdT1 p * wdT2 p * r) := by
  induction r using MonoidAlgebra.induction_on with
  | hM g =>
      rw [MonoidAlgebra.of_apply, wdT1, wdT2, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.single_mul_single, wdAtBideg_single, wdAtBideg_single, wwDiagAct,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      simp [toAdd_mul]
  | hadd x y hx hy => simp only [map_add, hx, hy, mul_add]
  | hsmul c x hx => simp only [map_smul, hx, mul_smul_comm]

/-- **`ψ_W` is `Λ`-linear for the diagonal action**: `ψ(T x) = (T ⊗ T) ψ(x)`. -/
theorem psiW_grGen_mul (p n : ℕ) (x : GroupRingZMod p) :
    psiW p n (grGen p * x) = wwDiagAct p (psiW p n x) := by
  rw [psiW_apply, psiW_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [wwDiagAct_atBideg, map_mul (wdDiag p), wdDiag_grGen]
  congr 1
  ring

end

end GroupApproximation.CharClass

open GroupApproximation.CharClass

#audit_axioms wdT2_pow_card
#audit_axioms wwDAll_atBideg
#audit_axioms psiW_chainMap
#audit_axioms psiW_grGen_mul
