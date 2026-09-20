import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TwoZero
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Meta.AxiomGuard
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span

/-!
# Interface: Tulenbaev's elements `X_{v,w}(t)` (lane k2-panin, input of F.4)

M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, Math. USSR Sb. 45 (1983), §1. Take
a column `v` over a commutative ring `B` and a row `w` that is a sum of rows `wᵏ ⊥ v`, each with two
zero coordinates. For `t` in the ideal `I(v)` of the coordinates of `v`, Tulenbaev puts
`X_{v,w}(t) = ∏ₖ X(v, t wᵏ)`. Here `X(v, u) = X_i(vᵢ u) [Xⁱ(v), X_i(u)]` for `uᵢ = 0`. The
column `v` need not be unimodular. These elements drive the proof of Prop 1.4(b), i.e. F.4
(`PaninAffine.Patching`).

This module states what F.4 consumes, as the structure `TulX r`:
* a family of maps `X : (Fin r → B) → (Fin r → B) → B → St_r(B)`, one for each ring `B`;
* the relations below. Each holds under the admissibility condition `AdmRow v w`
  (`w ∈ I(v) · v^⊥`) and `t ∈ I(v)`.

| field | relation | source |
|---|---|---|
| `nat` | natural in ring maps | the definition |
| `add` | `X_{v,w}(t) X_{v,w}(t') = X_{v,w}(t + t')` | T 1.1(b), (e) |
| `rowAdd` | `X_{v,w}(t) X_{v,w'}(t) = X_{v,w+w'}(t)` | T 1.3(a) |
| `smulRow` | `X_{v,cw}(t) = X_{v,w}(ct)` | T 1.3(a) |
| `smulCol` | `X_{cv,w}(t) = X_{v,w}(ct)` | T 1.1(d) |
| `colAdd` | `X_{v+cv',w}(t) = X_{v,w}(t) X_{v',w}(ct)`, for `w` in the span of the two-zero rows `⊥ v, v'` | T 1.3(c), 1.1(a) |
| `conj` | `γ X_{v,w}(t) γ⁻¹ = X_{π(γ)v, wπ(γ)⁻¹}(t)` | T 1.3(b), `r ≥ 5` |
| `proj` | `π(X_{v,w}(t)) = 1 + t v w` | vdK |
| `single` | `X_{eₖ,eₗ}(t) = xₖₗ(t)` | the definition |

The admissible rows `I(v) · v^⊥` are the ones Tulenbaev's Prop 1.4 uses (`w ∈ M_{1,r}(aᵖ A)` with
`aᵖ ∈ I(v)`). By the canonical decomposition `(u·v) w = ∑ᵢ<ⱼ wᵢⱼ`, each of them is a sum of two-zero
rows `⊥ v`. The set is stable under `GL_r(B)` and under ring maps.

**Owner of an instance:** bh-pal-linear-char0 (T 1.1–1.3, on k2-vdk's `VdK.Elements`). Target:
`∀ r, 5 ≤ r → TulX r`. Not root-wired.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace PaninAffine

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman Matrix

section Defs

variable {r : ℕ} {B : Type*} [CommRing B]

/-- The matrix `π(γ) ∈ E_r(B)` of a Steinberg element. -/
abbrev pMat (γ : SteinbergGroup (Fin r) B) : Matrix (Fin r) (Fin r) B :=
  ((projection γ : (Matrix (Fin r) (Fin r) B)ˣ) : Matrix (Fin r) (Fin r) B)

theorem pMat_mul (γ δ : SteinbergGroup (Fin r) B) : pMat (γ * δ) = pMat γ * pMat δ := by
  simp only [pMat, map_mul, Subgroup.coe_mul, Units.val_mul]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.pMat_mul

theorem pMat_one : pMat (1 : SteinbergGroup (Fin r) B) = 1 := by
  simp only [pMat, map_one, OneMemClass.coe_one, Units.val_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.pMat_one

theorem pMat_mul_inv (γ : SteinbergGroup (Fin r) B) : pMat γ * pMat γ⁻¹ = 1 := by
  rw [← pMat_mul, mul_inv_cancel, pMat_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.pMat_mul_inv

theorem pMat_inv_mul (γ : SteinbergGroup (Fin r) B) : pMat γ⁻¹ * pMat γ = 1 := by
  rw [← pMat_mul, inv_mul_cancel, pMat_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.pMat_inv_mul

theorem pMat_x (i j : Fin r) (hij : i ≠ j) (c : B) :
    pMat (x i j hij c) = 1 + Matrix.single i j c := by
  rw [pMat, projection_x]
  rfl

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.pMat_x

theorem pMat_ringMap {C : Type*} [CommRing C] (f : B →+* C) (γ : SteinbergGroup (Fin r) B) :
    pMat (ringMap f γ) = f.mapMatrix (pMat γ) := by
  rw [pMat, SteinbergBasic.projection_ringMap]
  rfl

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.pMat_ringMap

/-- The ideal `I(v)` of the coordinates of a column `v`. -/
abbrev coordIdeal (v : Fin r → B) : Ideal B :=
  Ideal.span (Set.range v)

/-- The rows orthogonal to `v`. -/
def orthSub (v : Fin r → B) : Submodule B (Fin r → B) where
  carrier := {u | u ⬝ᵥ v = 0}
  add_mem' := fun {x y} hx hy => by
    change (x + y) ⬝ᵥ v = 0
    rw [add_dotProduct, show x ⬝ᵥ v = 0 from hx, show y ⬝ᵥ v = 0 from hy, add_zero]
  zero_mem' := zero_dotProduct v
  smul_mem' := fun c x hx => by
    change (c • x) ⬝ᵥ v = 0
    rw [smul_dotProduct, show x ⬝ᵥ v = 0 from hx, smul_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.orthSub

theorem mem_orthSub {v u : Fin r → B} : u ∈ orthSub v ↔ u ⬝ᵥ v = 0 :=
  Iff.rfl

/-- **Admissible rows** for `X_{v,-}`: `w ∈ I(v) · v^⊥`. -/
def AdmRow (v w : Fin r → B) : Prop :=
  w ∈ coordIdeal v • orthSub v

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.AdmRow

theorem admRow_smul {v u : Fin r → B} {c : B} (hc : c ∈ coordIdeal v) (hu : u ⬝ᵥ v = 0) :
    AdmRow v (c • u) :=
  Submodule.smul_mem_smul hc hu

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.admRow_smul

theorem coordIdeal_single_eq_top (k : Fin r) : coordIdeal (Pi.single k (1 : B)) = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ⟨k, Pi.single_eq_same k 1⟩)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.coordIdeal_single_eq_top

theorem mem_coordIdeal {v : Fin r → B} (k : Fin r) : v k ∈ coordIdeal v :=
  Ideal.subset_span ⟨k, rfl⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.mem_coordIdeal

end Defs

/-- **Tulenbaev's elements `X_{v,w}(t)` and the relations F.4 consumes** (T 1.1–1.3). See the
module docstring for the table of fields and their sources. -/
structure TulX (r : ℕ) where
  /-- `X_{v,w}(t) ∈ St_r(B)`. Only its values on admissible data matter. -/
  X : ∀ {B : Type} [CommRing B], (Fin r → B) → (Fin r → B) → B → SteinbergGroup (Fin r) B
  nat : ∀ {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v w : Fin r → B) (t : B),
    AdmRow v w → t ∈ coordIdeal v → ringMap f (X v w t) = X (f ∘ v) (f ∘ w) (f t)
  add : ∀ {B : Type} [CommRing B] (v w : Fin r → B) (t t' : B), AdmRow v w →
    t ∈ coordIdeal v → t' ∈ coordIdeal v → X v w t * X v w t' = X v w (t + t')
  rowAdd : ∀ {B : Type} [CommRing B] (v w w' : Fin r → B) (t : B), AdmRow v w → AdmRow v w' →
    t ∈ coordIdeal v → X v w t * X v w' t = X v (w + w') t
  smulRow : ∀ {B : Type} [CommRing B] (v w : Fin r → B) (c t : B), AdmRow v w →
    t ∈ coordIdeal v → X v (c • w) t = X v w (c * t)
  smulCol : ∀ {B : Type} [CommRing B] (v w : Fin r → B) (c t : B), AdmRow v w →
    t ∈ coordIdeal (c • v) → X (c • v) w t = X v w (c * t)
  colAdd : ∀ {B : Type} [CommRing B] (v v' w : Fin r → B) (c t : B),
    w ∈ Submodule.span B (K2Found.TwoZero.twoZeroSet v v') → t ∈ coordIdeal v →
    c * t ∈ coordIdeal v' → t ∈ coordIdeal (v + c • v') →
    X (v + c • v') w t = X v w t * X v' w (c * t)
  conj : ∀ {B : Type} [CommRing B] (v w : Fin r → B) (t : B), AdmRow v w → t ∈ coordIdeal v →
    ∀ γ : SteinbergGroup (Fin r) B, γ * X v w t * γ⁻¹ = X (pMat γ *ᵥ v) (w ᵥ* pMat γ⁻¹) t
  proj : ∀ {B : Type} [CommRing B] (v w : Fin r → B) (t : B), AdmRow v w → t ∈ coordIdeal v →
    pMat (X v w t) = 1 + t • vecMulVec v w
  single : ∀ {B : Type} [CommRing B] (k l : Fin r) (hkl : k ≠ l) (t : B),
    X (Pi.single k 1) (Pi.single l 1) t = x k l hkl t

namespace TulX

variable {r : ℕ} (T : TulX r) {B : Type} [CommRing B]

theorem X_zero (v w : Fin r → B) (hw : AdmRow v w) : T.X v w 0 = 1 := by
  have h := T.add v w 0 0 hw (zero_mem _) (zero_mem _)
  rw [add_zero] at h
  exact mul_left_cancel (a := T.X v w 0) (h.trans (mul_one _).symm)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.TulX.X_zero

theorem X_neg (v w : Fin r → B) (t : B) (hw : AdmRow v w) (ht : t ∈ coordIdeal v) :
    T.X v w (-t) = (T.X v w t)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [T.add v w (-t) t hw (neg_mem ht) ht, neg_add_cancel, T.X_zero v w hw]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.TulX.X_neg

theorem pMat_X_inv (v w : Fin r → B) (t : B) (hw : AdmRow v w) (ht : t ∈ coordIdeal v) :
    pMat (T.X v w t)⁻¹ = 1 + (-t) • vecMulVec v w := by
  rw [← T.X_neg v w t hw ht, T.proj v w (-t) hw (neg_mem ht)]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.TulX.pMat_X_inv

theorem mulVec_one_add_smul_vecMulVec (s : B) (v v' w' : Fin r → B) (h : w' ⬝ᵥ v = 0) :
    (1 + s • vecMulVec v' w') *ᵥ v = v := by
  rw [add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, h, MulOpposite.op_zero, zero_smul,
    smul_zero, add_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.TulX.mulVec_one_add_smul_vecMulVec

theorem vecMul_one_add_smul_vecMulVec (s : B) (w v' w' : Fin r → B) (h : w ⬝ᵥ v' = 0) :
    w ᵥ* (1 + s • vecMulVec v' w') = w := by
  rw [vecMul_add, vecMul_one, vecMul_smul, vecMul_vecMulVec, h, zero_smul, smul_zero, add_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.TulX.vecMul_one_add_smul_vecMulVec

/-- **Commutation.** `X_{v,w}(t)` and `X_{v',w'}(t')` commute when `w' ⊥ v` and `w ⊥ v'`. -/
theorem commute_X (v w v' w' : Fin r → B) (t t' : B) (hw : AdmRow v w) (ht : t ∈ coordIdeal v)
    (hw' : AdmRow v' w') (ht' : t' ∈ coordIdeal v') (h1 : w' ⬝ᵥ v = 0) (h2 : w ⬝ᵥ v' = 0) :
    Commute (T.X v w t) (T.X v' w' t') := by
  have hc := T.conj v w t hw ht (T.X v' w' t')
  rw [T.proj v' w' t' hw' ht', T.pMat_X_inv v' w' t' hw' ht',
    mulVec_one_add_smul_vecMulVec t' v v' w' h1,
    vecMul_one_add_smul_vecMulVec (-t') w v' w' h2] at hc
  have hc' : T.X v' w' t' * T.X v w t = T.X v w t * T.X v' w' t' := by
    calc T.X v' w' t' * T.X v w t
        = T.X v' w' t' * T.X v w t * (T.X v' w' t')⁻¹ * T.X v' w' t' := by group
      _ = T.X v w t * T.X v' w' t' := by rw [hc]
  exact hc'.symm

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.TulX.commute_X

/-- **Conjugation onto a root.** If `γ` moves `v` to `c eₖ` (`c` a unit) and `w` to `d eₗ`, then
`γ X_{v,w}(t) γ⁻¹ = xₖₗ(c d t)`. -/
theorem conj_eq_x (v w : Fin r → B) (t : B) (hw : AdmRow v w) (ht : t ∈ coordIdeal v)
    (γ : SteinbergGroup (Fin r) B) (k l : Fin r) (hkl : k ≠ l) (c d : B) (hc : IsUnit c)
    (hv : pMat γ *ᵥ v = c • Pi.single k 1) (hw' : w ᵥ* pMat γ⁻¹ = d • Pi.single l 1) :
    γ * T.X v w t * γ⁻¹ = x k l hkl (c * d * t) := by
  have hkl' : Pi.single l (1 : B) ⬝ᵥ Pi.single k 1 = 0 := by
    rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hkl.symm]
  have htop : ∀ s : B, s ∈ coordIdeal (Pi.single k (1 : B)) := fun s => by
    rw [coordIdeal_single_eq_top]; exact Submodule.mem_top
  have hct : t ∈ coordIdeal (c • Pi.single k (1 : B)) := by
    have h1 : c ∈ coordIdeal (c • Pi.single k (1 : B)) := by
      have := mem_coordIdeal (v := c • (Pi.single k 1 : Fin r → B)) k
      rwa [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at this
    have h2 : (1 : B) ∈ coordIdeal (c • Pi.single k (1 : B)) := by
      have := Ideal.mul_mem_left _ (↑hc.unit⁻¹ : B) h1
      rwa [IsUnit.val_inv_mul] at this
    have := Ideal.mul_mem_left _ t h2
    rwa [mul_one] at this
  have hadm : AdmRow (Pi.single k (1 : B)) (Pi.single l 1) := by
    have := admRow_smul (v := Pi.single k (1 : B)) (htop 1) hkl'
    rwa [one_smul] at this
  have hadm' : AdmRow (Pi.single k (1 : B)) (d • Pi.single l 1) :=
    admRow_smul (htop d) hkl'
  rw [T.conj v w t hw ht γ, hv, hw', T.smulCol _ _ c t hadm' hct,
    T.smulRow _ _ d (c * t) hadm (htop _), T.single k l hkl]
  congr 1
  ring

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.TulX.conj_eq_x

end TulX

end PaninAffine
end BooneHigmanLinear
end GroupApproximation
