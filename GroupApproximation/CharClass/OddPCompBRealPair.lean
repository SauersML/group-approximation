import GroupApproximation.CharClass.OddPCompBRealDiag
import GroupApproximation.CharClass.OddPProductConcat
import Mathlib.Tactic.Module

/-!
# `R` on `W ⊗ W`: the pair terms of the Cartan realisation and their Leibniz formula

The realisation `B` of the Cartan comparison sends `e_j ⊗ σ` to the riffle of
`Σ_{AW splits σ = σ'·σ''} R_{σ',σ''}(ψ_W(e_j))`.  This file is `R` for two fixed simplices
`τ₁ : Δ^{m₁} → X`, `τ₂ : Δ^{m₂} → X`:

```text
R(T^s e_a ⊗ T^{s'} e_b) = (−1)^{b m₁} · concat(Φ(T^s e_a ⊗ τ₁), Φ(T^{s'} e_b ⊗ τ₂)),
```

a linear map `WWAll p → tupAllMod (ZMod p) X (2p)`, together with the two facts the chain-map
argument for `B` consumes:

* `realR_wwDiagAct` — the diagonal action of `T` on `W ⊗ W` goes to the blockwise rotation;
* `tupDAll_realR_single` — **the Leibniz formula**: the boundary of `R(w)` is `R(d_{W⊗W} w)` plus
  `(−1)^{a+b}` times the boundary terms in the simplices,
  `Σ_f (−1)^f R_{∂_f τ₁, τ₂}(w) + (−1)^{m₁} Σ_f (−1)^f R_{τ₁, ∂_f τ₂}(w)`.

The sign `(−1)^{b m₁}` is the Koszul sign of moving `e_b` past `τ₁`, and it is exactly what makes the
second resolution term of `d_{W⊗W}`, which carries `(−1)^a`, match the concatenation's Leibniz sign
`(−1)^{a + m₁}`: the two differ by `(−1)^{2 m₁}`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace CompBReal

section Signs

variable (p : ℕ)

/-- An integer sign acts as the same sign in `F_p`. -/
theorem zsmul_neg_one_pow {M : Type*} [AddCommGroup M] [Module (ZMod p) M] (n : ℕ) (x : M) :
    ((-1 : ℤ) ^ n) • x = ((-1 : ZMod p) ^ n) • x := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, h.neg_one_pow, one_smul, one_smul]
  · rw [h.neg_one_pow, h.neg_one_pow, neg_one_smul, neg_one_smul]

end Signs

section Pair

variable (p : ℕ) [NeZero p] [Fact p.Prime] (X : TopCat.{0})

/-- The simplicial half of `∂ Φ`, with the signs in `F_p`. -/
theorem phiGS_succ_zmod (a m' : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop (m' + 1) ⟶ X) :
    phiGS p X a c (m' + 1) τ
      = ∑ f : Fin (m' + 2), ((-1 : ZMod p) ^ (f : ℕ)) • phiG p X a m' c (faceMap X m' f τ) := by
  rw [phiGS_succ]
  exact Finset.sum_congr rfl fun f _ => zsmul_neg_one_pow p (f : ℕ) _

/-- `Φ(a, m, c, τ)` has total degree `a + m`, so the grading involution is the sign `(−1)^{a+m}`. -/
theorem tupSignAll_phiG (a m : ℕ) (c : GroupRingZMod p) (τ : stdSimplexTop m ⟶ X) :
    tupSignAll (ZMod p) X p (phiG p X a m c τ) = ((-1 : ZMod p) ^ (a + m)) • phiG p X a m c τ := by
  rw [phiG_eq, tupSignAll_tupIncl]

/-! ## 1. The pair term -/

/-- **The pair term** `concat(Φ(a, m₁, c₁, τ₁), Φ(b, m₂, c₂, τ₂))` in the `2p`-fold tensor power. -/
def pairG (a m₁ : ℕ) (c₁ : GroupRingZMod p) (τ₁ : stdSimplexTop m₁ ⟶ X) (b m₂ : ℕ)
    (c₂ : GroupRingZMod p) (τ₂ : stdSimplexTop m₂ ⟶ X) : tupAllMod (ZMod p) X (2 * p) :=
  tupConcatSq (ZMod p) X p (phiG p X a m₁ c₁ τ₁) (phiG p X b m₂ c₂ τ₂)

/-- **The Leibniz formula for a pair term.** -/
theorem tupDAll_pairG (a m₁ : ℕ) (c₁ : GroupRingZMod p) (τ₁ : stdSimplexTop m₁ ⟶ X) (b m₂ : ℕ)
    (c₂ : GroupRingZMod p) (τ₂ : stdSimplexTop m₂ ⟶ X) :
    tupDAll (ZMod p) X (2 * p) (pairG p X a m₁ c₁ τ₁ b m₂ c₂ τ₂)
      = tupConcatSq (ZMod p) X p (tupDAll (ZMod p) X p (phiG p X a m₁ c₁ τ₁))
          (phiG p X b m₂ c₂ τ₂)
        + ((-1 : ZMod p) ^ (a + m₁)) •
            tupConcatSq (ZMod p) X p (phiG p X a m₁ c₁ τ₁)
              (tupDAll (ZMod p) X p (phiG p X b m₂ c₂ τ₂)) := by
  rw [pairG, tupDAll_tupConcatSq, tupSignAll_phiG, map_smul, LinearMap.smul_apply]

theorem pairG_add_left (a m₁ : ℕ) (c₁ c₁' : GroupRingZMod p) (τ₁ : stdSimplexTop m₁ ⟶ X)
    (b m₂ : ℕ) (c₂ : GroupRingZMod p) (τ₂ : stdSimplexTop m₂ ⟶ X) :
    pairG p X a m₁ (c₁ + c₁') τ₁ b m₂ c₂ τ₂
      = pairG p X a m₁ c₁ τ₁ b m₂ c₂ τ₂ + pairG p X a m₁ c₁' τ₁ b m₂ c₂ τ₂ := by
  simp only [pairG]
  rw [phiG_add, map_add, LinearMap.add_apply]

theorem pairG_add_right (a m₁ : ℕ) (c₁ : GroupRingZMod p) (τ₁ : stdSimplexTop m₁ ⟶ X)
    (b m₂ : ℕ) (c₂ c₂' : GroupRingZMod p) (τ₂ : stdSimplexTop m₂ ⟶ X) :
    pairG p X a m₁ c₁ τ₁ b m₂ (c₂ + c₂') τ₂
      = pairG p X a m₁ c₁ τ₁ b m₂ c₂ τ₂ + pairG p X a m₁ c₁ τ₁ b m₂ c₂' τ₂ := by
  simp only [pairG]
  rw [phiG_add, map_add]

theorem pairG_zmod_smul_left (a m₁ : ℕ) (r : ZMod p) (c₁ : GroupRingZMod p)
    (τ₁ : stdSimplexTop m₁ ⟶ X) (b m₂ : ℕ) (c₂ : GroupRingZMod p) (τ₂ : stdSimplexTop m₂ ⟶ X) :
    pairG p X a m₁ (r • c₁) τ₁ b m₂ c₂ τ₂ = r • pairG p X a m₁ c₁ τ₁ b m₂ c₂ τ₂ := by
  simp only [pairG]
  rw [phiG_zmod_smul, map_smul, LinearMap.smul_apply]

theorem pairG_zmod_smul_right (a m₁ : ℕ) (c₁ : GroupRingZMod p) (τ₁ : stdSimplexTop m₁ ⟶ X)
    (b m₂ : ℕ) (r : ZMod p) (c₂ : GroupRingZMod p) (τ₂ : stdSimplexTop m₂ ⟶ X) :
    pairG p X a m₁ c₁ τ₁ b m₂ (r • c₂) τ₂ = r • pairG p X a m₁ c₁ τ₁ b m₂ c₂ τ₂ := by
  simp only [pairG]
  rw [phiG_zmod_smul, map_smul]

/-- **The blockwise rotation of a pair term** shifts both exponents of `T`. -/
theorem tupBlockRotAll_pairG (a m₁ : ℕ) (s : ZMod p) (τ₁ : stdSimplexTop m₁ ⟶ X) (b m₂ : ℕ)
    (s' : ZMod p) (τ₂ : stdSimplexTop m₂ ⟶ X) :
    tupBlockRotAll (ZMod p) X p (pairG p X a m₁ (monoGen p s) τ₁ b m₂ (monoGen p s') τ₂)
      = pairG p X a m₁ (monoGen p (1 + s)) τ₁ b m₂ (monoGen p (1 + s')) τ₂ := by
  simp only [pairG]
  rw [tupBlockRotAll_tupConcatSq, phiG_monoGen_one_add, phiG_monoGen_one_add]

/-! ## 2. `R` on `W ⊗ W` -/

/-- **`R` on `W ⊗ W`** for two fixed simplices: `T^s e_a ⊗ T^{s'} e_b` goes to
`(−1)^{b m₁} concat(Φ(T^s e_a ⊗ τ₁), Φ(T^{s'} e_b ⊗ τ₂))`. -/
def realR (m₁ : ℕ) (τ₁ : stdSimplexTop m₁ ⟶ X) (m₂ : ℕ) (τ₂ : stdSimplexTop m₂ ⟶ X) :
    WWAll p →ₗ[ZMod p] tupAllMod (ZMod p) X (2 * p) :=
  Finsupp.linearCombination (ZMod p) (fun w : WWIdx p =>
    ((-1 : ZMod p) ^ (w.2.2.1 * m₁)) •
      pairG p X w.1 m₁ (monoGen p w.2.1) τ₁ w.2.2.1 m₂ (monoGen p w.2.2.2) τ₂)

theorem realR_single (m₁ : ℕ) (τ₁ : stdSimplexTop m₁ ⟶ X) (m₂ : ℕ) (τ₂ : stdSimplexTop m₂ ⟶ X)
    (a : ℕ) (s : ZMod p) (b : ℕ) (s' : ZMod p) :
    realR p X m₁ τ₁ m₂ τ₂ (Finsupp.single ((a, s, b, s') : WWIdx p) 1)
      = ((-1 : ZMod p) ^ (b * m₁)) • pairG p X a m₁ (monoGen p s) τ₁ b m₂ (monoGen p s') τ₂ := by
  simp only [realR, Finsupp.linearCombination_single, one_smul]

/-- **The diagonal action of `T` on `W ⊗ W` goes to the blockwise rotation.** -/
theorem realR_wwDiagAct (m₁ : ℕ) (τ₁ : stdSimplexTop m₁ ⟶ X) (m₂ : ℕ)
    (τ₂ : stdSimplexTop m₂ ⟶ X) (x : WWAll p) :
    realR p X m₁ τ₁ m₂ τ₂ (wwDiagAct p x)
      = tupBlockRotAll (ZMod p) X p (realR p X m₁ τ₁ m₂ τ₂ x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single w c =>
    obtain ⟨a, s, b, s'⟩ := w
    rw [← Finsupp.smul_single_one]
    simp only [map_smul]
    congr 1
    simp only [wwDiagAct, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, realR_single,
      map_smul, tupBlockRotAll_pairG]

/-- `R` on a bidegree, with a group-ring coefficient on the left factor. -/
theorem realR_atBideg_inl (m₁ : ℕ) (τ₁ : stdSimplexTop m₁ ⟶ X) (m₂ : ℕ)
    (τ₂ : stdSimplexTop m₂ ⟶ X) (a b : ℕ) (l : GroupRingZMod p) (s s' : ZMod p) :
    realR p X m₁ τ₁ m₂ τ₂ (wdAtBideg p a b (wdInl p l * wdMono p s s'))
      = ((-1 : ZMod p) ^ (b * m₁)) •
          pairG p X a m₁ (l * monoGen p s) τ₁ b m₂ (monoGen p s') τ₂ := by
  induction l using MonoidAlgebra.induction_on with
  | hM g =>
    have h1 : wdInl p (MonoidAlgebra.of (ZMod p) (Multiplicative (ZMod p)) g) * wdMono p s s'
        = MonoidAlgebra.single (g * Multiplicative.ofAdd s, Multiplicative.ofAdd s') (1 : ZMod p) := by
      simp only [MonoidAlgebra.of_apply, wdInl_single, wdMono, MonoidAlgebra.single_mul_single,
        Prod.mk_mul_mk, one_mul, mul_one]
    have h2 : MonoidAlgebra.of (ZMod p) (Multiplicative (ZMod p)) g * monoGen p s
        = monoGen p (Multiplicative.toAdd (g * Multiplicative.ofAdd s)) := by
      simp only [MonoidAlgebra.of_apply, monoGen, MonoidAlgebra.single_mul_single, one_mul,
        ofAdd_toAdd]
    rw [h1, wdAtBideg_single, h2]
    simp only [realR_single, toAdd_ofAdd]
  | hadd x y hx hy =>
    simp only [map_add, add_mul, hx, hy, pairG_add_left, smul_add]
  | hsmul r x hx =>
    simp only [map_smul, smul_mul_assoc, hx, pairG_zmod_smul_left]
    rw [smul_comm]

/-- `R` on a bidegree, with a group-ring coefficient on the right factor. -/
theorem realR_atBideg_inr (m₁ : ℕ) (τ₁ : stdSimplexTop m₁ ⟶ X) (m₂ : ℕ)
    (τ₂ : stdSimplexTop m₂ ⟶ X) (a b : ℕ) (l : GroupRingZMod p) (s s' : ZMod p) :
    realR p X m₁ τ₁ m₂ τ₂ (wdAtBideg p a b (wdInr p l * wdMono p s s'))
      = ((-1 : ZMod p) ^ (b * m₁)) •
          pairG p X a m₁ (monoGen p s) τ₁ b m₂ (l * monoGen p s') τ₂ := by
  induction l using MonoidAlgebra.induction_on with
  | hM g =>
    have h1 : wdInr p (MonoidAlgebra.of (ZMod p) (Multiplicative (ZMod p)) g) * wdMono p s s'
        = MonoidAlgebra.single (Multiplicative.ofAdd s, g * Multiplicative.ofAdd s') (1 : ZMod p) := by
      simp only [MonoidAlgebra.of_apply, wdInr_single, wdMono, MonoidAlgebra.single_mul_single,
        Prod.mk_mul_mk, one_mul, mul_one]
    have h2 : MonoidAlgebra.of (ZMod p) (Multiplicative (ZMod p)) g * monoGen p s'
        = monoGen p (Multiplicative.toAdd (g * Multiplicative.ofAdd s')) := by
      simp only [MonoidAlgebra.of_apply, monoGen, MonoidAlgebra.single_mul_single, one_mul,
        ofAdd_toAdd]
    rw [h1, wdAtBideg_single, h2]
    simp only [realR_single, toAdd_ofAdd]
  | hadd x y hx hy =>
    simp only [map_add, add_mul, hx, hy, pairG_add_right, smul_add]
  | hsmul r x hx =>
    simp only [map_smul, smul_mul_assoc, hx, pairG_zmod_smul_right]
    rw [smul_comm]

/-! ## 3. The boundary terms in the simplices -/

/-- The boundary terms of `R` in the first simplex: `Σ_f (−1)^f R_{∂_f τ₁, τ₂}`, and `0` in simplex
degree `0`. -/
def realRbdL : (m₁ : ℕ) → (stdSimplexTop m₁ ⟶ X) → (m₂ : ℕ) → (stdSimplexTop m₂ ⟶ X) →
    (WWAll p →ₗ[ZMod p] tupAllMod (ZMod p) X (2 * p))
  | 0, _, _, _ => 0
  | m' + 1, τ₁, m₂, τ₂ =>
      ∑ f : Fin (m' + 2), ((-1 : ZMod p) ^ (f : ℕ)) • realR p X m' (faceMap X m' f τ₁) m₂ τ₂

/-- The boundary terms of `R` in the second simplex: `Σ_f (−1)^f R_{τ₁, ∂_f τ₂}`, and `0` in simplex
degree `0`. -/
def realRbdR (m₁ : ℕ) (τ₁ : stdSimplexTop m₁ ⟶ X) : (m₂ : ℕ) → (stdSimplexTop m₂ ⟶ X) →
    (WWAll p →ₗ[ZMod p] tupAllMod (ZMod p) X (2 * p))
  | 0, _ => 0
  | m' + 1, τ₂ =>
      ∑ f : Fin (m' + 2), ((-1 : ZMod p) ^ (f : ℕ)) • realR p X m₁ τ₁ m' (faceMap X m' f τ₂)

@[simp] theorem realRbdL_zero (τ₁ : stdSimplexTop 0 ⟶ X) (m₂ : ℕ) (τ₂ : stdSimplexTop m₂ ⟶ X) :
    realRbdL p X 0 τ₁ m₂ τ₂ = 0 := rfl

@[simp] theorem realRbdL_succ (m' : ℕ) (τ₁ : stdSimplexTop (m' + 1) ⟶ X) (m₂ : ℕ)
    (τ₂ : stdSimplexTop m₂ ⟶ X) :
    realRbdL p X (m' + 1) τ₁ m₂ τ₂
      = ∑ f : Fin (m' + 2), ((-1 : ZMod p) ^ (f : ℕ)) • realR p X m' (faceMap X m' f τ₁) m₂ τ₂ :=
  rfl

@[simp] theorem realRbdR_zero (m₁ : ℕ) (τ₁ : stdSimplexTop m₁ ⟶ X) (τ₂ : stdSimplexTop 0 ⟶ X) :
    realRbdR p X m₁ τ₁ 0 τ₂ = 0 := rfl

@[simp] theorem realRbdR_succ (m₁ : ℕ) (τ₁ : stdSimplexTop m₁ ⟶ X) (m' : ℕ)
    (τ₂ : stdSimplexTop (m' + 1) ⟶ X) :
    realRbdR p X m₁ τ₁ (m' + 1) τ₂
      = ∑ f : Fin (m' + 2), ((-1 : ZMod p) ^ (f : ℕ)) • realR p X m₁ τ₁ m' (faceMap X m' f τ₂) :=
  rfl

/-! ## 4. The four components of the Leibniz formula -/

/-- The left resolution half. -/
theorem realR_wdLeftBd (m₁ : ℕ) (τ₁ : stdSimplexTop m₁ ⟶ X) (m₂ : ℕ)
    (τ₂ : stdSimplexTop m₂ ⟶ X) (a : ℕ) (s : ZMod p) (b : ℕ) (s' : ZMod p) :
    realR p X m₁ τ₁ m₂ τ₂ (wdLeftBd p a b (wdMono p s s'))
      = ((-1 : ZMod p) ^ (b * m₁)) •
          tupConcatSq (ZMod p) X p (phiGW p X a m₁ (monoGen p s) τ₁)
            (phiG p X b m₂ (monoGen p s') τ₂) := by
  cases a with
  | zero =>
    simp only [wdLeftBd_zero, map_zero, phiGW_zero, LinearMap.zero_apply, smul_zero]
  | succ a' =>
    rw [wdLeftBd_succ, wdCAlt_wdT1, realR_atBideg_inl, phiGW_succ]
    rfl

/-- The right resolution half. -/
theorem realR_wdRightBd (m₁ : ℕ) (τ₁ : stdSimplexTop m₁ ⟶ X) (m₂ : ℕ)
    (τ₂ : stdSimplexTop m₂ ⟶ X) (a : ℕ) (s : ZMod p) (b : ℕ) (s' : ZMod p) :
    realR p X m₁ τ₁ m₂ τ₂ (wdRightBd p a b (wdMono p s s'))
      = ((-1 : ZMod p) ^ (b * m₁) * (-1 : ZMod p) ^ (a + m₁)) •
          tupConcatSq (ZMod p) X p (phiG p X a m₁ (monoGen p s) τ₁)
            (phiGW p X b m₂ (monoGen p s') τ₂) := by
  cases b with
  | zero =>
    simp only [wdRightBd_zero, map_zero, phiGW_zero, smul_zero]
  | succ b' =>
    rw [wdRightBd_succ, map_smul, wdCAlt_wdT2, realR_atBideg_inr, phiGW_succ, smul_smul]
    refine congrArg₂ (fun (r : ZMod p) (x : tupAllMod (ZMod p) X (2 * p)) => r • x) ?_ rfl
    rw [← pow_add, ← pow_add]
    exact neg_one_pow_eq_of_add_two_mul m₁ (by ring)

/-- The simplicial half in the first simplex. -/
theorem realRbdL_single_eq (m₁ : ℕ) (τ₁ : stdSimplexTop m₁ ⟶ X) (m₂ : ℕ)
    (τ₂ : stdSimplexTop m₂ ⟶ X) (a : ℕ) (s : ZMod p) (b : ℕ) (s' : ZMod p) :
    ((-1 : ZMod p) ^ (a + b)) •
        realRbdL p X m₁ τ₁ m₂ τ₂ (Finsupp.single ((a, s, b, s') : WWIdx p) 1)
      = ((-1 : ZMod p) ^ (b * m₁) * (-1 : ZMod p) ^ a) •
          tupConcatSq (ZMod p) X p (phiGS p X a (monoGen p s) m₁ τ₁)
            (phiG p X b m₂ (monoGen p s') τ₂) := by
  cases m₁ with
  | zero =>
    simp only [realRbdL_zero, LinearMap.zero_apply, smul_zero, phiGS_zero, map_zero]
  | succ m' =>
    rw [realRbdL_succ, phiGS_succ_zmod]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, realR_single, map_sum, map_smul,
      Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun f _ => ?_
    refine congrArg₂ (fun (r : ZMod p) (x : tupAllMod (ZMod p) X (2 * p)) => r • x) ?_ rfl
    ring

/-- The simplicial half in the second simplex. -/
theorem realRbdR_single_eq (m₁ : ℕ) (τ₁ : stdSimplexTop m₁ ⟶ X) (m₂ : ℕ)
    (τ₂ : stdSimplexTop m₂ ⟶ X) (a : ℕ) (s : ZMod p) (b : ℕ) (s' : ZMod p) :
    ((-1 : ZMod p) ^ (a + b)) •
        (((-1 : ZMod p) ^ m₁) •
          realRbdR p X m₁ τ₁ m₂ τ₂ (Finsupp.single ((a, s, b, s') : WWIdx p) 1))
      = ((-1 : ZMod p) ^ (b * m₁) * (-1 : ZMod p) ^ (a + m₁) * (-1 : ZMod p) ^ b) •
          tupConcatSq (ZMod p) X p (phiG p X a m₁ (monoGen p s) τ₁)
            (phiGS p X b (monoGen p s') m₂ τ₂) := by
  cases m₂ with
  | zero =>
    simp only [realRbdR_zero, LinearMap.zero_apply, smul_zero, phiGS_zero, map_zero]
  | succ m' =>
    rw [realRbdR_succ, phiGS_succ_zmod]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, realR_single, map_sum, map_smul,
      Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun f _ => ?_
    refine congrArg₂ (fun (r : ZMod p) (x : tupAllMod (ZMod p) X (2 * p)) => r • x) ?_ rfl
    ring

/-! ## 5. The Leibniz formula -/

/-- **The Leibniz formula for `R`**, on a basis vector `T^s e_a ⊗ T^{s'} e_b`:
`∂ R(w) = R(d_{W⊗W} w) + (−1)^{a+b} (Σ_f (−1)^f R_{∂_f τ₁, τ₂}(w) + (−1)^{m₁} Σ_f (−1)^f R_{τ₁, ∂_f τ₂}(w))`. -/
theorem tupDAll_realR_single (m₁ : ℕ) (τ₁ : stdSimplexTop m₁ ⟶ X) (m₂ : ℕ)
    (τ₂ : stdSimplexTop m₂ ⟶ X) (a : ℕ) (s : ZMod p) (b : ℕ) (s' : ZMod p) :
    tupDAll (ZMod p) X (2 * p)
        (realR p X m₁ τ₁ m₂ τ₂ (Finsupp.single ((a, s, b, s') : WWIdx p) 1))
      = realR p X m₁ τ₁ m₂ τ₂ (wwDAll p (Finsupp.single ((a, s, b, s') : WWIdx p) 1))
        + ((-1 : ZMod p) ^ (a + b)) •
            (realRbdL p X m₁ τ₁ m₂ τ₂ (Finsupp.single ((a, s, b, s') : WWIdx p) 1)
              + ((-1 : ZMod p) ^ m₁) •
                realRbdR p X m₁ τ₁ m₂ τ₂ (Finsupp.single ((a, s, b, s') : WWIdx p) 1)) := by
  simp only [wwDAll, Finsupp.linearCombination_single, one_smul, wdBdGen]
  rw [map_add, realR_wdLeftBd, realR_wdRightBd, smul_add, realRbdL_single_eq, realRbdR_single_eq,
    realR_single, map_smul, tupDAll_pairG, tupDAll_phiG, tupDAll_phiG]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_add, smul_smul]
  module

end Pair

end CompBReal

end

end GroupApproximation.CharClass

open GroupApproximation.CharClass.CompBReal

#audit_axioms tupDAll_pairG
#audit_axioms realR_wwDiagAct
#audit_axioms realR_atBideg_inl
#audit_axioms realR_wdRightBd
#audit_axioms tupDAll_realR_single
