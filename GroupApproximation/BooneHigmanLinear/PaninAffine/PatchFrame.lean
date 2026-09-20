import GroupApproximation.BooneHigmanLinear.PaninAffine.PatchAlg
import GroupApproximation.Meta.AxiomGuard
import Mathlib.RingTheory.Localization.Integer

/-!
# Tulenbaev's operators `T_ij(c)` on the orbit set (lane k2-panin, F.4)

M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, proof of Prop 1.4(b). Let `a, b` be
comaximal non-zero-divisors of `A`. The orbit set is `V = St(A_a) × St(A_b) / ~`, where
`(α γ_a, β) ~ (α, γ_b β)` for `γ ∈ St(A)` (`patchSetoid`). For `c ∈ A_{ab}` we have
`x_ij(c) = x_ij(c') · x_ij(c'')` with `c' ∈ A_a` and `c'' = jb (aᴺ s)` `a`-adically small. The
operator acts by
  `T_ij(c) [α, β] = [x_ij(c') α, X_{v,aᵖw}(aᵖ s) β]`.
Here `v = a^{m₁} π(α)⁻¹ eᵢ` and `w = a^{m₂} eⱼ π(α)`, cleared of denominators over `A` (a *frame*,
`IsFrame`), and `N = m₁ + m₂ + 2p`. This is Tulenbaev's formula with the partition of unity
already applied to `c`. The element `X_{v,aᵖw}(aᵖ s) ∈ St(A_b)` lifts `α⁻¹ x_ij(c'') α`. The
column `v` is not unimodular over `A_b`, which is why `TulX` is needed.

This module proves that `T_ij(c)` is well defined (`Tfun`, `Tfun_mk`):
* `opV_split`: independence of the splitting of `c`, via `zariski_diff`;
* `Xf_refine` and `Frame.join`: independence of the frame;
* `opV_rep`: independence of the representative `(α, β)`, via `TulX.conj`.

The Steinberg relations and the resulting action are in `PaninAffine.Patching`. Not root-wired.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace PaninAffine

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman Matrix

section ColRow

variable {r : ℕ} {B : Type*} [CommRing B]

/-- Column `i` of `π(α)⁻¹`. -/
abbrev colOf (α : SteinbergGroup (Fin r) B) (i : Fin r) : Fin r → B :=
  pMat α⁻¹ *ᵥ Pi.single i 1

/-- Row `j` of `π(α)`. -/
abbrev rowOf (α : SteinbergGroup (Fin r) B) (j : Fin r) : Fin r → B :=
  Pi.single j 1 ᵥ* pMat α

theorem rowOf_dot_colOf (α : SteinbergGroup (Fin r) B) (j i : Fin r) :
    rowOf α j ⬝ᵥ colOf α i = Pi.single i (1 : B) j := by
  show (Pi.single j 1 ᵥ* pMat α) ⬝ᵥ (pMat α⁻¹ *ᵥ Pi.single i 1) = _
  rw [dotProduct_mulVec, vecMul_vecMul, pMat_mul_inv, vecMul_one, single_one_dotProduct]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.rowOf_dot_colOf

theorem pMat_mulVec_colOf (α : SteinbergGroup (Fin r) B) (i : Fin r) :
    pMat α *ᵥ colOf α i = Pi.single i 1 := by
  show pMat α *ᵥ (pMat α⁻¹ *ᵥ Pi.single i 1) = _
  rw [mulVec_mulVec, pMat_mul_inv, one_mulVec]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.pMat_mulVec_colOf

theorem rowOf_vecMul_pMat_inv (α : SteinbergGroup (Fin r) B) (j : Fin r) :
    rowOf α j ᵥ* pMat α⁻¹ = Pi.single j 1 := by
  show Pi.single j 1 ᵥ* pMat α ᵥ* pMat α⁻¹ = _
  rw [vecMul_vecMul, pMat_mul_inv, vecMul_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.rowOf_vecMul_pMat_inv

theorem pMat_x_inv (k l : Fin r) (hkl : k ≠ l) (e : B) :
    pMat (x k l hkl e)⁻¹ = 1 + Matrix.single k l (-e) := by
  rw [← x_neg, pMat_x]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.pMat_x_inv

theorem vecMul_single' (v : Fin r → B) (k l : Fin r) (e : B) :
    v ᵥ* Matrix.single k l e = (e * v k) • Pi.single l 1 := by
  rw [← mulVec_transpose, transpose_single, single_mulVec_eq]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.vecMul_single'

theorem colOf_x_mul (k l : Fin r) (hkl : k ≠ l) (e : B) (α : SteinbergGroup (Fin r) B)
    (i : Fin r) : colOf (x k l hkl e * α) i = colOf α i + (-e * Pi.single i (1 : B) l) • colOf α k := by
  show pMat (x k l hkl e * α)⁻¹ *ᵥ Pi.single i 1 =
    pMat α⁻¹ *ᵥ Pi.single i 1 + (-e * Pi.single i (1 : B) l) • (pMat α⁻¹ *ᵥ Pi.single k 1)
  rw [mul_inv_rev, pMat_mul, pMat_x_inv, ← mulVec_mulVec, add_mulVec, one_mulVec,
    single_mulVec_eq, mulVec_add, mulVec_smul]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.colOf_x_mul

theorem rowOf_x_mul (k l : Fin r) (hkl : k ≠ l) (e : B) (α : SteinbergGroup (Fin r) B)
    (j : Fin r) : rowOf (x k l hkl e * α) j = rowOf α j + (e * Pi.single j (1 : B) k) • rowOf α l := by
  show Pi.single j 1 ᵥ* pMat (x k l hkl e * α) =
    Pi.single j 1 ᵥ* pMat α + (e * Pi.single j (1 : B) k) • (Pi.single l 1 ᵥ* pMat α)
  rw [pMat_mul, pMat_x, ← vecMul_vecMul, vecMul_add, vecMul_one, vecMul_single', add_vecMul,
    smul_vecMul]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.rowOf_x_mul

theorem colOf_x_mul_of_ne {k l : Fin r} (hkl : k ≠ l) (e : B) (α : SteinbergGroup (Fin r) B)
    {i : Fin r} (hli : l ≠ i) : colOf (x k l hkl e * α) i = colOf α i := by
  rw [colOf_x_mul, Pi.single_eq_of_ne hli, mul_zero, zero_smul, add_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.colOf_x_mul_of_ne

theorem rowOf_x_mul_of_ne {k l : Fin r} (hkl : k ≠ l) (e : B) (α : SteinbergGroup (Fin r) B)
    {j : Fin r} (hjk : j ≠ k) : rowOf (x k l hkl e * α) j = rowOf α j := by
  rw [rowOf_x_mul, Pi.single_eq_of_ne hjk.symm, mul_zero, zero_smul, add_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.rowOf_x_mul_of_ne

end ColRow

/-- **A frame**: Tulenbaev's parameters `m₁, m₂, p` and the integral column `v`, row `w`, and a
row `u` with `u v = aᵖ`. -/
structure Frame (A : Type*) (r : ℕ) where
  m1 : ℕ
  m2 : ℕ
  p : ℕ
  v : Fin r → A
  w : Fin r → A
  u : Fin r → A

/-- The `a`-adic size `N = m₁ + m₂ + 2p` of the `A_b`-part of the splitting. -/
def Frame.N {A : Type*} {r : ℕ} (Φ : Frame A r) : ℕ :=
  Φ.m1 + Φ.m2 + 2 * Φ.p

section Frames

variable {r : ℕ} {A : Type} [CommRing A]

/-- `Φ` is a frame for the column `cl` and the row `rl` over `A_a`. -/
def IsFrame (a : A) (Φ : Frame A r) (cl rl : Fin r → Localization.Away a) : Prop :=
  loc a ∘ Φ.v = loc a a ^ Φ.m1 • cl ∧ loc a ∘ Φ.w = loc a a ^ Φ.m2 • rl ∧
    Φ.u ⬝ᵥ Φ.v = a ^ Φ.p ∧ Φ.w ⬝ᵥ Φ.v = 0

/-- The element `X_{f v, f(aᵖ w)}(f(a)ᵖ s)` over `C`, for `f : A → C`. -/
noncomputable def Xf (T : TulX r) (a : A) (Φ : Frame A r) {C : Type} [CommRing C] (f : A →+* C)
    (s : C) : SteinbergGroup (Fin r) C :=
  T.X (f ∘ Φ.v) (f ∘ (a ^ Φ.p • Φ.w)) (f a ^ Φ.p * s)

variable {a : A} {Φ : Frame A r}

theorem Frame.pow_mem (hu : Φ.u ⬝ᵥ Φ.v = a ^ Φ.p) {C : Type} [CommRing C] (f : A →+* C) :
    f a ^ Φ.p ∈ coordIdeal (f ∘ Φ.v) := by
  rw [← map_pow, ← hu, ← comp_dotProduct]
  exact dotProduct_mem_coordIdeal _ _

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Frame.pow_mem

theorem Frame.adm (hu : Φ.u ⬝ᵥ Φ.v = a ^ Φ.p) (hw : Φ.w ⬝ᵥ Φ.v = 0) {C : Type} [CommRing C]
    (f : A →+* C) : AdmRow (f ∘ Φ.v) (f ∘ (a ^ Φ.p • Φ.w)) := by
  rw [comp_smul', map_pow]
  exact admRow_smul (Frame.pow_mem hu f) (by rw [comp_dotProduct, hw, map_zero])

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Frame.adm

theorem Frame.param_mem (hu : Φ.u ⬝ᵥ Φ.v = a ^ Φ.p) {C : Type} [CommRing C] (f : A →+* C)
    (s : C) : f a ^ Φ.p * s ∈ coordIdeal (f ∘ Φ.v) :=
  Ideal.mul_mem_right _ _ (Frame.pow_mem hu f)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Frame.param_mem

theorem Frame.adm_base (hu : Φ.u ⬝ᵥ Φ.v = a ^ Φ.p) (hw : Φ.w ⬝ᵥ Φ.v = 0) :
    AdmRow Φ.v (a ^ Φ.p • Φ.w) :=
  admRow_smul (by rw [← hu]; exact dotProduct_mem_coordIdeal _ _) hw

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Frame.adm_base

theorem Frame.param_mem_base (hu : Φ.u ⬝ᵥ Φ.v = a ^ Φ.p) (μ : A) :
    a ^ Φ.p * μ ∈ coordIdeal Φ.v :=
  Ideal.mul_mem_right _ _ (by rw [← hu]; exact dotProduct_mem_coordIdeal _ _)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Frame.param_mem_base

variable (T : TulX r)

theorem Xf_add (hu : Φ.u ⬝ᵥ Φ.v = a ^ Φ.p) (hw : Φ.w ⬝ᵥ Φ.v = 0) {C : Type} [CommRing C]
    (f : A →+* C) (s s' : C) : Xf T a Φ f s * Xf T a Φ f s' = Xf T a Φ f (s + s') := by
  unfold Xf
  rw [T.add _ _ _ _ (Frame.adm hu hw f) (Frame.param_mem hu f s) (Frame.param_mem hu f s'),
    mul_add]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Xf_add

theorem Xf_zero (hu : Φ.u ⬝ᵥ Φ.v = a ^ Φ.p) (hw : Φ.w ⬝ᵥ Φ.v = 0) {C : Type} [CommRing C]
    (f : A →+* C) : Xf T a Φ f 0 = 1 := by
  unfold Xf
  rw [mul_zero]
  exact T.X_zero _ _ (Frame.adm hu hw f)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Xf_zero

theorem Xf_ringMap (hu : Φ.u ⬝ᵥ Φ.v = a ^ Φ.p) (hw : Φ.w ⬝ᵥ Φ.v = 0) {C : Type} [CommRing C]
    (f : A →+* C) (μ : A) :
    ringMap f (T.X Φ.v (a ^ Φ.p • Φ.w) (a ^ Φ.p * μ)) = Xf T a Φ f (f μ) := by
  rw [T.nat f Φ.v (a ^ Φ.p • Φ.w) (a ^ Φ.p * μ) (Frame.adm_base hu hw)
    (Frame.param_mem_base hu μ), Xf, map_mul, map_pow]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Xf_ringMap

/-- **Refining a frame** by `v ↦ aᵉ v`, `w ↦ a^{e'} w` rescales the parameter. -/
theorem Xf_refine {Φ' : Frame A r} (e e' : ℕ) (hv : Φ'.v = a ^ e • Φ.v)
    (hw : Φ'.w = a ^ e' • Φ.w) (hp : Φ.p ≤ Φ'.p) (hu : Φ.u ⬝ᵥ Φ.v = a ^ Φ.p)
    (hwo : Φ.w ⬝ᵥ Φ.v = 0) (hu' : Φ'.u ⬝ᵥ Φ'.v = a ^ Φ'.p) {C : Type} [CommRing C]
    (f : A →+* C) (s : C) :
    Xf T a Φ' f s = Xf T a Φ f (f a ^ (2 * Φ'.p + e + e' - 2 * Φ.p) * s) := by
  have hI' := Frame.pow_mem hu' f
  rw [hv, comp_smul', map_pow] at hI'
  have hI := Frame.pow_mem hu f
  have hIp' : f a ^ Φ'.p ∈ coordIdeal (f ∘ Φ.v) := by
    rw [show Φ'.p = Φ.p + (Φ'.p - Φ.p) by omega, pow_add]
    exact Ideal.mul_mem_right _ _ hI
  have hW : (f ∘ Φ.w) ⬝ᵥ (f ∘ Φ.v) = 0 := by rw [comp_dotProduct, hwo, map_zero]
  have hadm1 : AdmRow (f ∘ Φ.v) (f a ^ (Φ'.p + e') • (f ∘ Φ.w)) := by
    refine admRow_smul ?_ hW
    rw [pow_add]
    exact Ideal.mul_mem_right _ _ hIp'
  have hadm2 : AdmRow (f ∘ Φ.v) (f a ^ Φ.p • (f ∘ Φ.w)) := admRow_smul hI hW
  have hsplit : f a ^ (Φ'.p + e') • (f ∘ Φ.w) =
      f a ^ (Φ'.p + e' - Φ.p) • (f a ^ Φ.p • (f ∘ Φ.w)) := by
    rw [smul_smul, ← pow_add, show Φ'.p + e' - Φ.p + Φ.p = Φ'.p + e' by omega]
  unfold Xf
  rw [hv, hw, smul_smul, ← pow_add]
  simp only [comp_smul', map_pow]
  rw [T.smulCol _ _ _ _ hadm1 (Ideal.mul_mem_right _ _ hI'), hsplit,
    T.smulRow _ _ _ _ hadm2 (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hIp'))]
  congr 1
  have hK : Φ'.p + e' - Φ.p + (e + Φ'.p) = Φ.p + (2 * Φ'.p + e + e' - 2 * Φ.p) := by omega
  calc f a ^ (Φ'.p + e' - Φ.p) * (f a ^ e * (f a ^ Φ'.p * s))
      = f a ^ (Φ'.p + e' - Φ.p + (e + Φ'.p)) * s := by rw [pow_add, pow_add]; ring
    _ = f a ^ (Φ.p + (2 * Φ'.p + e + e' - 2 * Φ.p)) * s := by rw [hK]
    _ = f a ^ Φ.p * (f a ^ (2 * Φ'.p + e + e' - 2 * Φ.p) * s) := by rw [pow_add]; ring

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Xf_refine

/-- The common refinement of two frames. -/
def Frame.join (a : A) (Φ₁ Φ₂ : Frame A r) : Frame A r where
  m1 := Φ₁.m1 + Φ₂.m1
  m2 := Φ₁.m2 + Φ₂.m2
  p := Φ₂.p + Φ₂.m1 + Φ₁.p
  v := a ^ Φ₂.m1 • Φ₁.v
  w := a ^ Φ₂.m2 • Φ₁.w
  u := a ^ Φ₂.p • Φ₁.u

theorem Frame.join_isFrame {Φ₁ Φ₂ : Frame A r} {cl rl : Fin r → Localization.Away a}
    (h₁ : IsFrame a Φ₁ cl rl) : IsFrame a (Frame.join a Φ₁ Φ₂) cl rl := by
  obtain ⟨hv, hw, hu, hwo⟩ := h₁
  refine ⟨?_, ?_, ?_, ?_⟩
  · show loc a ∘ (a ^ Φ₂.m1 • Φ₁.v) = loc a a ^ (Φ₁.m1 + Φ₂.m1) • cl
    rw [comp_smul', map_pow, hv, smul_smul, ← pow_add, add_comm Φ₂.m1]
  · show loc a ∘ (a ^ Φ₂.m2 • Φ₁.w) = loc a a ^ (Φ₁.m2 + Φ₂.m2) • rl
    rw [comp_smul', map_pow, hw, smul_smul, ← pow_add, add_comm Φ₂.m2]
  · show (a ^ Φ₂.p • Φ₁.u) ⬝ᵥ (a ^ Φ₂.m1 • Φ₁.v) = a ^ (Φ₂.p + Φ₂.m1 + Φ₁.p)
    rw [smul_dotProduct, dotProduct_smul, hu, smul_eq_mul, smul_eq_mul]
    ring
  · show (a ^ Φ₂.m2 • Φ₁.w) ⬝ᵥ (a ^ Φ₂.m1 • Φ₁.v) = 0
    rw [smul_dotProduct, dotProduct_smul, hwo, smul_zero, smul_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Frame.join_isFrame

theorem Frame.join_v {Φ₁ Φ₂ : Frame A r} {cl rl : Fin r → Localization.Away a}
    (ha : a ∈ nonZeroDivisors A) (h₁ : IsFrame a Φ₁ cl rl) (h₂ : IsFrame a Φ₂ cl rl) :
    a ^ Φ₂.m1 • Φ₁.v = a ^ Φ₁.m1 • Φ₂.v := by
  apply comp_injective (loc_injective ha)
  show loc a ∘ (a ^ Φ₂.m1 • Φ₁.v) = loc a ∘ (a ^ Φ₁.m1 • Φ₂.v)
  simp only [comp_smul', map_pow]
  rw [h₁.1, h₂.1, smul_smul, smul_smul, mul_comm]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Frame.join_v

theorem Frame.join_w {Φ₁ Φ₂ : Frame A r} {cl rl : Fin r → Localization.Away a}
    (ha : a ∈ nonZeroDivisors A) (h₁ : IsFrame a Φ₁ cl rl) (h₂ : IsFrame a Φ₂ cl rl) :
    a ^ Φ₂.m2 • Φ₁.w = a ^ Φ₁.m2 • Φ₂.w := by
  apply comp_injective (loc_injective ha)
  show loc a ∘ (a ^ Φ₂.m2 • Φ₁.w) = loc a ∘ (a ^ Φ₁.m2 • Φ₂.w)
  simp only [comp_smul', map_pow]
  rw [h₁.2.1, h₂.2.1, smul_smul, smul_smul, mul_comm]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Frame.join_w

/-- Moving a frame by `γ ∈ St(A)`: `v ↦ π(γ)⁻¹ v`, `w ↦ w π(γ)`. -/
def Frame.move (Φ : Frame A r) (γ : SteinbergGroup (Fin r) A) : Frame A r where
  m1 := Φ.m1
  m2 := Φ.m2
  p := Φ.p
  v := pMat γ⁻¹ *ᵥ Φ.v
  w := Φ.w ᵥ* pMat γ
  u := Φ.u ᵥ* pMat γ

theorem Frame.move_isFrame (α : SteinbergGroup (Fin r) (Localization.Away a))
    (γ : SteinbergGroup (Fin r) A) {i j : Fin r}
    (h : IsFrame a Φ (colOf α i) (rowOf α j)) :
    IsFrame a (Φ.move γ) (colOf (α * ringMap (loc a) γ) i) (rowOf (α * ringMap (loc a) γ) j) := by
  obtain ⟨hv, hw, hu, hwo⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · show loc a ∘ (pMat γ⁻¹ *ᵥ Φ.v) = loc a a ^ Φ.m1 •
      (pMat (α * ringMap (loc a) γ)⁻¹ *ᵥ Pi.single i 1)
    rw [comp_mulVec, ← pMat_ringMap, map_inv, hv, mulVec_smul, mul_inv_rev, pMat_mul,
      ← mulVec_mulVec]
  · show loc a ∘ (Φ.w ᵥ* pMat γ) = loc a a ^ Φ.m2 •
      (Pi.single j 1 ᵥ* pMat (α * ringMap (loc a) γ))
    rw [comp_vecMul, ← pMat_ringMap, hw, smul_vecMul, pMat_mul, ← vecMul_vecMul]
  · show (Φ.u ᵥ* pMat γ) ⬝ᵥ (pMat γ⁻¹ *ᵥ Φ.v) = a ^ Φ.p
    rw [dotProduct_mulVec, vecMul_vecMul, pMat_mul_inv, vecMul_one, hu]
  · show (Φ.w ᵥ* pMat γ) ⬝ᵥ (pMat γ⁻¹ *ᵥ Φ.v) = 0
    rw [dotProduct_mulVec, vecMul_vecMul, pMat_mul_inv, vecMul_one, hwo]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Frame.move_isFrame

theorem Xf_move (hu : Φ.u ⬝ᵥ Φ.v = a ^ Φ.p) (hwo : Φ.w ⬝ᵥ Φ.v = 0) {C : Type} [CommRing C]
    (f : A →+* C) (γ : SteinbergGroup (Fin r) A) (s : C) :
    Xf T a (Φ.move γ) f s = (ringMap f γ)⁻¹ * Xf T a Φ f s * ringMap f γ := by
  have hc := T.conj (f ∘ Φ.v) (f ∘ (a ^ Φ.p • Φ.w)) (f a ^ Φ.p * s) (Frame.adm hu hwo f)
    (Frame.param_mem hu f s) (ringMap f γ)⁻¹
  rw [inv_inv] at hc
  unfold Xf
  rw [hc]
  congr 1
  · show f ∘ (pMat γ⁻¹ *ᵥ Φ.v) = _
    rw [comp_mulVec, ← pMat_ringMap, map_inv]
  · show f ∘ (a ^ Φ.p • (Φ.w ᵥ* pMat γ)) = _
    rw [← smul_vecMul, comp_vecMul, ← pMat_ringMap]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Xf_move

end Frames

section Orbit

variable {r : ℕ} {A : Type} [CommRing A]

/-- The data of a Zariski square: `a, b` comaximal non-zero-divisors. -/
structure ZData (a b : A) : Prop where
  ha : a ∈ nonZeroDivisors A
  hb : b ∈ nonZeroDivisors A
  hab : IsCoprime a b

/-- `A_a` and `A_b` Steinberg pairs. -/
abbrev StPair (r : ℕ) (a b : A) : Type :=
  SteinbergGroup (Fin r) (Localization.Away a) × SteinbergGroup (Fin r) (Localization.Away b)

variable (r) in
/-- **The orbit relation** `(α, β) ~ (α γ_a, γ_b⁻¹ β)`. -/
def patchSetoid (a b : A) : Setoid (StPair r a b) where
  r P Q := ∃ γ : SteinbergGroup (Fin r) A,
    Q.1 = P.1 * ringMap (loc a) γ ∧ P.2 = ringMap (loc b) γ * Q.2
  iseqv :=
    { refl := fun P => ⟨1, by rw [map_one, mul_one], by rw [map_one, one_mul]⟩
      symm := fun {P Q} h => by
        obtain ⟨γ, h1, h2⟩ := h
        exact ⟨γ⁻¹, by rw [h1, map_inv, mul_inv_cancel_right],
          by rw [h2, map_inv, inv_mul_cancel_left]⟩
      trans := fun {P Q R} h h' => by
        obtain ⟨γ, h1, h2⟩ := h
        obtain ⟨δ, h3, h4⟩ := h'
        exact ⟨γ * δ, by rw [h3, h1, map_mul, mul_assoc], by rw [h2, h4, map_mul, mul_assoc]⟩ }

variable (r) in
/-- **The orbit set** `V`. -/
abbrev PatchV (a b : A) : Type :=
  Quotient (patchSetoid r a b)

theorem pmk_eq {a b : A} {P Q : StPair r a b} (γ : SteinbergGroup (Fin r) A)
    (h1 : Q.1 = P.1 * ringMap (loc a) γ) (h2 : P.2 = ringMap (loc b) γ * Q.2) :
    (Quotient.mk (patchSetoid r a b) P : PatchV r a b) = Quotient.mk _ Q :=
  Quotient.sound ⟨γ, h1, h2⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.pmk_eq

/-- A **valid tuple** for `T_ij(c)` at `α`: a frame `Φ` and a splitting `c = c' + jb (aᴺ s)`. -/
def Valid (a b : A) (α : SteinbergGroup (Fin r) (Localization.Away a)) (i j : Fin r)
    (c : Localization.Away (a * b)) (Φ : Frame A r) (c' : Localization.Away a)
    (s : Localization.Away b) : Prop :=
  IsFrame a Φ (colOf α i) (rowOf α j) ∧ c = ja a b c' + jb a b (loc b a ^ Φ.N * s)

variable (T : TulX r)

/-- The value of `T_ij(c)` computed from a valid tuple. -/
noncomputable def opV (a b : A) {i j : Fin r} (hij : i ≠ j) (P : StPair r a b) (Φ : Frame A r)
    (c' : Localization.Away a) (s : Localization.Away b) : PatchV r a b :=
  Quotient.mk _ (x i j hij c' * P.1, Xf T a Φ (loc b) s * P.2)

variable {a b : A}

/-- **Independence of the splitting.** -/
theorem opV_split (hz : ZData a b) {i j : Fin r} (hij : i ≠ j) (P : StPair r a b)
    {Φ : Frame A r} (hΦ : IsFrame a Φ (colOf P.1 i) (rowOf P.1 j))
    {c₁ c₂ : Localization.Away a} {s₁ s₂ : Localization.Away b}
    (h : ja a b c₁ + jb a b (loc b a ^ Φ.N * s₁) = ja a b c₂ + jb a b (loc b a ^ Φ.N * s₂)) :
    opV T a b hij P Φ c₁ s₁ = opV T a b hij P Φ c₂ s₂ := by
  obtain ⟨hv, hw, hu, hwo⟩ := hΦ
  have h1 : ja a b (c₁ - c₂) = jb a b (loc b a ^ Φ.N * (s₂ - s₁)) := by
    rw [map_sub, mul_sub, map_sub]
    linear_combination h
  obtain ⟨μ, hμ1, hμ2⟩ := zariski_diff hz.ha hz.hb hz.hab h1
  have hγa : ringMap (loc a) (T.X Φ.v (a ^ Φ.p • Φ.w) (a ^ Φ.p * μ)) =
      T.X (loc a ∘ Φ.v) (loc a ∘ (a ^ Φ.p • Φ.w)) (loc a a ^ Φ.p * loc a μ) :=
    Xf_ringMap T hu hwo (loc a) μ
  have hv' : pMat P.1 *ᵥ (loc a ∘ Φ.v) = loc a a ^ Φ.m1 • Pi.single i 1 := by
    rw [hv, mulVec_smul, pMat_mulVec_colOf]
  have hw' : (loc a ∘ (a ^ Φ.p • Φ.w)) ᵥ* pMat P.1⁻¹ =
      (loc a a ^ Φ.p * loc a a ^ Φ.m2) • Pi.single j 1 := by
    rw [comp_smul', hw, map_pow, smul_smul, smul_vecMul, rowOf_vecMul_pMat_inv]
  have hconj := T.conj_eq_x (loc a ∘ Φ.v) (loc a ∘ (a ^ Φ.p • Φ.w))
    (loc a a ^ Φ.p * loc a μ) (Frame.adm hu hwo _) (Frame.param_mem hu _ _) P.1 i j hij _ _
    ((isUnit_loc_self a).pow Φ.m1) hv' hw'
  have hparam : loc a a ^ Φ.m1 * (loc a a ^ Φ.p * loc a a ^ Φ.m2) * (loc a a ^ Φ.p * loc a μ) =
      loc a (a ^ Φ.N * μ) := by
    rw [Frame.N, map_mul, map_pow]
    ring
  have hA : x i j hij (loc a (a ^ Φ.N * μ)) * P.1 =
      P.1 * ringMap (loc a) (T.X Φ.v (a ^ Φ.p • Φ.w) (a ^ Φ.p * μ)) := by
    rw [hγa, ← hparam, ← hconj]
    group
  have hB : Xf T a Φ (loc b) s₂ =
      ringMap (loc b) (T.X Φ.v (a ^ Φ.p • Φ.w) (a ^ Φ.p * μ)) * Xf T a Φ (loc b) s₁ := by
    rw [Xf_ringMap T hu hwo (loc b) μ, Xf_add T hu hwo, ← hμ2, sub_add_cancel]
  have hc : c₁ = c₂ + loc a (a ^ Φ.N * μ) := by
    rw [← hμ1]
    ring
  unfold opV
  rw [hc, ← x_mul, mul_assoc, hA, hB]
  symm
  exact pmk_eq (T.X Φ.v (a ^ Φ.p • Φ.w) (a ^ Φ.p * μ)) (by dsimp only; rw [mul_assoc])
    (by dsimp only; rw [mul_assoc])

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.opV_split

/-- **Independence of the tuple.** -/
theorem opV_wd (hz : ZData a b) {i j : Fin r} (hij : i ≠ j) (P : StPair r a b)
    {c : Localization.Away (a * b)} {Φ₁ Φ₂ : Frame A r} {c₁ c₂ : Localization.Away a}
    {s₁ s₂ : Localization.Away b} (h₁ : Valid a b P.1 i j c Φ₁ c₁ s₁)
    (h₂ : Valid a b P.1 i j c Φ₂ c₂ s₂) :
    opV T a b hij P Φ₁ c₁ s₁ = opV T a b hij P Φ₂ c₂ s₂ := by
  obtain ⟨hΦ₁, hc₁⟩ := h₁
  obtain ⟨hΦ₂, hc₂⟩ := h₂
  have hΦ₃ : IsFrame a (Frame.join a Φ₁ Φ₂) (colOf P.1 i) (rowOf P.1 j) :=
    Frame.join_isFrame hΦ₁
  obtain ⟨q, hq⟩ := zariski_split hz.hab c
  obtain ⟨c₃, s₃, -, hc₃, -⟩ := hq (Frame.join a Φ₁ Φ₂).N
  -- the refinement over `Φ₁`
  have hX₁ := Xf_refine T (Φ := Φ₁) (Φ' := Frame.join a Φ₁ Φ₂) Φ₂.m1 Φ₂.m2 rfl rfl
    (by show Φ₁.p ≤ Φ₂.p + Φ₂.m1 + Φ₁.p; omega) hΦ₁.2.2.1 hΦ₁.2.2.2 hΦ₃.2.2.1 (loc b) s₃
  have hN₁ : (Frame.join a Φ₁ Φ₂).N =
      Φ₁.N + (2 * (Frame.join a Φ₁ Φ₂).p + Φ₂.m1 + Φ₂.m2 - 2 * Φ₁.p) := by
    simp only [Frame.N, Frame.join]
    omega
  -- the refinement over `Φ₂`
  have hX₂ := Xf_refine T (Φ := Φ₂) (Φ' := Frame.join a Φ₁ Φ₂) Φ₁.m1 Φ₁.m2
    (Frame.join_v hz.ha hΦ₁ hΦ₂) (Frame.join_w hz.ha hΦ₁ hΦ₂)
    (by show Φ₂.p ≤ Φ₂.p + Φ₂.m1 + Φ₁.p; omega) hΦ₂.2.2.1 hΦ₂.2.2.2 hΦ₃.2.2.1 (loc b) s₃
  have hN₂ : (Frame.join a Φ₁ Φ₂).N =
      Φ₂.N + (2 * (Frame.join a Φ₁ Φ₂).p + Φ₁.m1 + Φ₁.m2 - 2 * Φ₂.p) := by
    simp only [Frame.N, Frame.join]
    omega
  have e₁ : opV T a b hij P Φ₁ c₁ s₁ = opV T a b hij P Φ₁ c₃
      (loc b a ^ (2 * (Frame.join a Φ₁ Φ₂).p + Φ₂.m1 + Φ₂.m2 - 2 * Φ₁.p) * s₃) := by
    refine opV_split T hz hij P hΦ₁ (hc₁.symm.trans (hc₃.trans ?_))
    rw [hN₁, pow_add, mul_assoc]
  have e₂ : opV T a b hij P Φ₂ c₂ s₂ = opV T a b hij P Φ₂ c₃
      (loc b a ^ (2 * (Frame.join a Φ₁ Φ₂).p + Φ₁.m1 + Φ₁.m2 - 2 * Φ₂.p) * s₃) := by
    refine opV_split T hz hij P hΦ₂ (hc₂.symm.trans (hc₃.trans ?_))
    rw [hN₂, pow_add, mul_assoc]
  rw [e₁, e₂]
  unfold opV
  rw [← hX₁, ← hX₂]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.opV_wd

/-- **Independence of the representative.** -/
theorem opV_rep {i j : Fin r} (hij : i ≠ j) {P Q : StPair r a b}
    (γ : SteinbergGroup (Fin r) A) (h1 : Q.1 = P.1 * ringMap (loc a) γ)
    (h2 : P.2 = ringMap (loc b) γ * Q.2) {c : Localization.Away (a * b)} {Φ : Frame A r}
    {c' : Localization.Away a} {s : Localization.Away b} (hV : Valid a b P.1 i j c Φ c' s) :
    Valid a b Q.1 i j c (Φ.move γ) c' s ∧
      opV T a b hij P Φ c' s = opV T a b hij Q (Φ.move γ) c' s := by
  obtain ⟨hΦ, hc⟩ := hV
  have hΦ' := Frame.move_isFrame P.1 γ hΦ
  rw [← h1] at hΦ'
  refine ⟨⟨hΦ', hc⟩, ?_⟩
  unfold opV
  rw [Xf_move T hΦ.2.2.1 hΦ.2.2.2 (loc b) γ s]
  refine pmk_eq γ (by dsimp only; rw [h1, mul_assoc]) ?_
  dsimp only
  rw [h2]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.opV_rep

theorem exists_clear (y : A) {ι : Type*} [Finite ι] (u : ι → Localization.Away y) :
    ∃ (m : ℕ) (v : ι → A), ∀ k, loc y (v k) = loc y y ^ m * u k := by
  obtain ⟨⟨_, m, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (M := Submonoid.powers y) (S := Localization.Away y) u
  have h : ∀ k, ∃ z : A, loc y z = y ^ m • u k := fun k => RingHom.mem_rangeS.mp (hb k)
  choose v hv using h
  exact ⟨m, v, fun k => by rw [hv k, Algebra.smul_def, map_pow]⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.exists_clear

theorem exists_frame (hz : ZData a b) (α : SteinbergGroup (Fin r) (Localization.Away a))
    {i j : Fin r} (hij : i ≠ j) : ∃ Φ : Frame A r, IsFrame a Φ (colOf α i) (rowOf α j) := by
  obtain ⟨m1, v, hv⟩ := exists_clear a (colOf α i)
  obtain ⟨m2, w, hw⟩ := exists_clear a (rowOf α j)
  obtain ⟨q, u, hu⟩ := exists_clear a (rowOf α i)
  have hv' : loc a ∘ v = loc a a ^ m1 • colOf α i := funext hv
  have hw' : loc a ∘ w = loc a a ^ m2 • rowOf α j := funext hw
  have hu' : loc a ∘ u = loc a a ^ q • rowOf α i := funext hu
  refine ⟨⟨m1, m2, q + m1, v, w, u⟩, hv', hw', ?_, ?_⟩
  · apply loc_injective hz.ha
    show loc a (u ⬝ᵥ v) = loc a (a ^ (q + m1))
    rw [← comp_dotProduct, hu', hv', smul_dotProduct, dotProduct_smul, rowOf_dot_colOf,
      Pi.single_eq_same, map_pow, pow_add, smul_eq_mul, smul_eq_mul, mul_one]
  · apply loc_injective hz.ha
    show loc a (w ⬝ᵥ v) = loc a 0
    rw [← comp_dotProduct, hw', hv', smul_dotProduct, dotProduct_smul, rowOf_dot_colOf,
      Pi.single_eq_of_ne hij.symm, smul_zero, smul_zero, map_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.exists_frame

theorem exists_valid (hz : ZData a b) (α : SteinbergGroup (Fin r) (Localization.Away a))
    {i j : Fin r} (hij : i ≠ j) (c : Localization.Away (a * b)) :
    ∃ t : Frame A r × Localization.Away a × Localization.Away b,
      Valid a b α i j c t.1 t.2.1 t.2.2 := by
  obtain ⟨Φ, hΦ⟩ := exists_frame hz α hij
  obtain ⟨q, hq⟩ := zariski_split hz.hab c
  obtain ⟨c', s, -, hc, -⟩ := hq Φ.N
  exact ⟨(Φ, c', s), hΦ, hc⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.exists_valid

/-- `T_ij(c)` on representatives, through a chosen valid tuple. -/
noncomputable def Tpre (hz : ZData a b) {i j : Fin r} (hij : i ≠ j)
    (c : Localization.Away (a * b)) (P : StPair r a b) : PatchV r a b :=
  opV T a b hij P (exists_valid hz P.1 hij c).choose.1 (exists_valid hz P.1 hij c).choose.2.1
    (exists_valid hz P.1 hij c).choose.2.2

theorem Tpre_eq (hz : ZData a b) {i j : Fin r} (hij : i ≠ j) {c : Localization.Away (a * b)}
    (P : StPair r a b) {Φ : Frame A r} {c' : Localization.Away a} {s : Localization.Away b}
    (hV : Valid a b P.1 i j c Φ c' s) : Tpre T hz hij c P = opV T a b hij P Φ c' s :=
  opV_wd T hz hij P (exists_valid hz P.1 hij c).choose_spec hV

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Tpre_eq

/-- **Tulenbaev's operator `T_ij(c)` on the orbit set.** -/
noncomputable def Tfun (hz : ZData a b) {i j : Fin r} (hij : i ≠ j)
    (c : Localization.Away (a * b)) : PatchV r a b → PatchV r a b :=
  Quotient.lift (Tpre T hz hij c) fun P Q hPQ => by
    obtain ⟨γ, h1, h2⟩ := hPQ
    obtain ⟨hV', hop⟩ := opV_rep T hij γ h1 h2 (exists_valid hz P.1 hij c).choose_spec
    calc Tpre T hz hij c P = opV T a b hij P (exists_valid hz P.1 hij c).choose.1
          (exists_valid hz P.1 hij c).choose.2.1 (exists_valid hz P.1 hij c).choose.2.2 := rfl
      _ = _ := hop
      _ = Tpre T hz hij c Q := (Tpre_eq T hz hij Q hV').symm

theorem Tfun_mk (hz : ZData a b) {i j : Fin r} (hij : i ≠ j) {c : Localization.Away (a * b)}
    (P : StPair r a b) {Φ : Frame A r} {c' : Localization.Away a} {s : Localization.Away b}
    (hV : Valid a b P.1 i j c Φ c' s) :
    Tfun T hz hij c (Quotient.mk _ P) = opV T a b hij P Φ c' s :=
  Tpre_eq T hz hij P hV

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Tfun_mk

end Orbit

end PaninAffine
end BooneHigmanLinear
end GroupApproximation
