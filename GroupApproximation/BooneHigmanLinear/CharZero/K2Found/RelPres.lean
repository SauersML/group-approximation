import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdK
import Mathlib.RingTheory.Ideal.BigOperators
import GroupApproximation.Meta.AxiomGuard

/-!
# Tulenbaev's relative Steinberg group, presented (k2-poly, piece F.2)

M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, Math. USSR Sb. 45 (1983), Def 1.5.
Let `𝔄` be an ideal of a commutative ring `A`. The group `St(A, 𝔄)` (`RelSt I A 𝔄`) has one
generator `X_{v,w}` for each pair `(v, w)` (`RMem 𝔄`) with:
* `v ∈ E(A) eᵢ` (`IsEColumn`);
* `w` a row with entries in `𝔄`;
* `w v = 0`.

The relations are Tulenbaev's (1.1)–(1.3):
* `add`: `X_{v,w} X_{v,w'} = X_{v,w+w'}`;
* `conj`: `X_{v,w} X_{v',w'} X_{v,w}⁻¹ = X_{v' + (w v') v, w' - (w' v) w}` (vdK's `conjPair`);
* `frame`: `X_{b v + v', w} = X_{v, b w} X_{v', w}`, if `u v = 0`, `u v' = 1` for some row `u` and
  `w v = 0`.

Each relation is imposed whenever all the pairs in it are generators. `smulPair g` is the action
`(v, w) ↦ (g v, w g⁻¹)` of `E(A)` on the generating pairs (`smulPair_mem`, `smulPair_conjPair`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace RelPres

open Matrix
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (conjPair)

section Pairs

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A]

/-- `v ∈ E(A) eᵢ` for some `i`. -/
def IsEColumn (v : I → A) : Prop :=
  ∃ g ∈ elementaryGroup I A, ∃ i, v = (g : Matrix I I A) *ᵥ Pi.single i 1

theorem isEColumn_single (i : I) : IsEColumn (Pi.single i (1 : A)) :=
  ⟨1, one_mem _, i, by rw [Units.val_one, one_mulVec]⟩

#audit_axioms isEColumn_single

theorem IsEColumn.isUnimodular {v : I → A} (hv : IsEColumn v) : VdK.IsUnimodular v := by
  obtain ⟨g, -, i, rfl⟩ := hv
  refine ⟨Pi.single i 1 ᵥ* ((g⁻¹ : (Matrix I I A)ˣ) : Matrix I I A), ?_⟩
  rw [dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one, single_dotProduct,
    Pi.single_eq_same, mul_one]

#audit_axioms IsEColumn.isUnimodular

/-- The generating pairs of `St(A, 𝔄)`. -/
def RMem (𝔄 : Ideal A) (p : (I → A) × (I → A)) : Prop :=
  IsEColumn p.1 ∧ (∀ k, p.2 k ∈ 𝔄) ∧ p.2 ⬝ᵥ p.1 = 0

variable {𝔄 : Ideal A}

theorem RMem.mem_U {p : (I → A) × (I → A)} (hp : RMem 𝔄 p) : p ∈ VdK.U I A :=
  VdK.mem_U.2 ⟨hp.1.isUnimodular, hp.2.2⟩

theorem RMem.add {v w w' : I → A} (h : RMem 𝔄 (v, w)) (h' : RMem 𝔄 (v, w')) :
    RMem 𝔄 (v, w + w') :=
  ⟨h.1, fun k => add_mem (h.2.1 k) (h'.2.1 k), by
    change (w + w') ⬝ᵥ v = 0
    rw [add_dotProduct, h.2.2, h'.2.2, add_zero]⟩

theorem RMem.neg {v w : I → A} (h : RMem 𝔄 (v, w)) : RMem 𝔄 (v, -w) :=
  ⟨h.1, fun k => neg_mem (h.2.1 k), by
    change (-w) ⬝ᵥ v = 0
    rw [neg_dotProduct, h.2.2, neg_zero]⟩

theorem RMem.zero {v w : I → A} (h : RMem 𝔄 (v, w)) : RMem 𝔄 (v, 0) :=
  ⟨h.1, fun _ => zero_mem _, by change (0 : I → A) ⬝ᵥ v = 0; simp⟩

theorem RMem.smul {v w : I → A} (b : A) (h : RMem 𝔄 (v, w)) : RMem 𝔄 (v, b • w) :=
  ⟨h.1, fun k => 𝔄.mul_mem_left b (h.2.1 k), by
    change (b • w) ⬝ᵥ v = 0
    rw [smul_dotProduct, h.2.2, smul_zero]⟩

/-- `(v, w) ↦ (g v, w g⁻¹)`. -/
def smulPair (g : (Matrix I I A)ˣ) (p : (I → A) × (I → A)) : (I → A) × (I → A) :=
  ((g : Matrix I I A) *ᵥ p.1, p.2 ᵥ* ((g⁻¹ : (Matrix I I A)ˣ) : Matrix I I A))

theorem smulPair_dot (g : (Matrix I I A)ˣ) (w v : I → A) :
    (w ᵥ* ((g⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) ⬝ᵥ ((g : Matrix I I A) *ᵥ v) = w ⬝ᵥ v := by
  rw [dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one]

#audit_axioms smulPair_dot

omit [DecidableEq I] in
theorem vecMul_mem (M : Matrix I I A) {w : I → A} (hw : ∀ k, w k ∈ 𝔄) (k : I) :
    (w ᵥ* M) k ∈ 𝔄 := by
  simp only [vecMul, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hw j)

#audit_axioms vecMul_mem

theorem smulPair_mem {g : (Matrix I I A)ˣ} (hg : g ∈ elementaryGroup I A)
    {p : (I → A) × (I → A)} (hp : RMem 𝔄 p) : RMem 𝔄 (smulPair g p) := by
  obtain ⟨⟨h, hh, i, hv⟩, hw, hwv⟩ := hp
  refine ⟨⟨g * h, mul_mem hg hh, i, ?_⟩, vecMul_mem _ hw, ?_⟩
  · change (g : Matrix I I A) *ᵥ p.1 = _
    rw [hv, Units.val_mul, mulVec_mulVec]
  · change (p.2 ᵥ* ((g⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) ⬝ᵥ ((g : Matrix I I A) *ᵥ p.1) = 0
    rw [smulPair_dot]
    exact hwv

#audit_axioms smulPair_mem

theorem smulPair_one (p : (I → A) × (I → A)) : smulPair 1 p = p := by
  refine Prod.ext ?_ ?_
  · change ((1 : (Matrix I I A)ˣ) : Matrix I I A) *ᵥ p.1 = p.1
    rw [Units.val_one, one_mulVec]
  · change p.2 ᵥ* (((1 : (Matrix I I A)ˣ)⁻¹ : (Matrix I I A)ˣ) : Matrix I I A) = p.2
    rw [inv_one, Units.val_one, vecMul_one]

#audit_axioms smulPair_one

theorem smulPair_mul (g h : (Matrix I I A)ˣ) (p : (I → A) × (I → A)) :
    smulPair (g * h) p = smulPair g (smulPair h p) := by
  refine Prod.ext ?_ ?_
  · change ((g * h : (Matrix I I A)ˣ) : Matrix I I A) *ᵥ p.1 =
      (g : Matrix I I A) *ᵥ ((h : Matrix I I A) *ᵥ p.1)
    rw [Units.val_mul, mulVec_mulVec]
  · change p.2 ᵥ* (((g * h)⁻¹ : (Matrix I I A)ˣ) : Matrix I I A) =
      (p.2 ᵥ* ((h⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) ᵥ* ((g⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)
    rw [mul_inv_rev, Units.val_mul, vecMul_vecMul]

#audit_axioms smulPair_mul

theorem smulPair_conjPair (g : (Matrix I I A)ˣ) (p q : (I → A) × (I → A)) :
    smulPair g (conjPair p q) = conjPair (smulPair g p) (smulPair g q) := by
  refine Prod.ext ?_ ?_
  · change (g : Matrix I I A) *ᵥ (q.1 + (p.2 ⬝ᵥ q.1) • p.1) =
      (g : Matrix I I A) *ᵥ q.1 + ((p.2 ᵥ* ((g⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) ⬝ᵥ
        ((g : Matrix I I A) *ᵥ q.1)) • ((g : Matrix I I A) *ᵥ p.1)
    rw [smulPair_dot, mulVec_add, mulVec_smul]
  · change (q.2 - (q.2 ⬝ᵥ p.1) • p.2) ᵥ* ((g⁻¹ : (Matrix I I A)ˣ) : Matrix I I A) =
      q.2 ᵥ* ((g⁻¹ : (Matrix I I A)ˣ) : Matrix I I A) -
        ((q.2 ᵥ* ((g⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) ⬝ᵥ ((g : Matrix I I A) *ᵥ p.1)) •
          (p.2 ᵥ* ((g⁻¹ : (Matrix I I A)ˣ) : Matrix I I A))
    rw [smulPair_dot, sub_vecMul, smul_vecMul]

#audit_axioms smulPair_conjPair

end Pairs

section Presentation

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A]

variable (I A) in
/-- The generators `X_{v,w}` of `St(A, 𝔄)`. -/
abbrev RGen (𝔄 : Ideal A) : Type _ :=
  {p : (I → A) × (I → A) // RMem 𝔄 p}

/-- Tulenbaev's relations (1.1)–(1.3). -/
inductive IsRel (𝔄 : Ideal A) : FreeGroup (RGen I A 𝔄) → Prop
  | add (v w w' : I → A) (h₁ : RMem 𝔄 (v, w)) (h₂ : RMem 𝔄 (v, w')) (h₃ : RMem 𝔄 (v, w + w')) :
      IsRel 𝔄 (FreeGroup.of (⟨(v, w), h₁⟩ : RGen I A 𝔄) * FreeGroup.of ⟨(v, w'), h₂⟩ *
        (FreeGroup.of ⟨(v, w + w'), h₃⟩)⁻¹)
  | conj (p q : (I → A) × (I → A)) (hp : RMem 𝔄 p) (hq : RMem 𝔄 q)
      (hc : RMem 𝔄 (conjPair p q)) :
      IsRel 𝔄 (FreeGroup.of (⟨p, hp⟩ : RGen I A 𝔄) * FreeGroup.of ⟨q, hq⟩ *
        (FreeGroup.of ⟨p, hp⟩)⁻¹ * (FreeGroup.of ⟨conjPair p q, hc⟩)⁻¹)
  | frame (v v' w u : I → A) (b : A) (_hu : u ⬝ᵥ v = 0) (_hu' : u ⬝ᵥ v' = 1) (_hw : w ⬝ᵥ v = 0)
      (h₁ : RMem 𝔄 (b • v + v', w)) (h₂ : RMem 𝔄 (v, b • w)) (h₃ : RMem 𝔄 (v', w)) :
      IsRel 𝔄 (FreeGroup.of (⟨(b • v + v', w), h₁⟩ : RGen I A 𝔄) *
        (FreeGroup.of ⟨(v, b • w), h₂⟩ * FreeGroup.of ⟨(v', w), h₃⟩)⁻¹)

variable (I A) in
/-- The relator set of `St(A, 𝔄)`. -/
def rels (𝔄 : Ideal A) : Set (FreeGroup (RGen I A 𝔄)) :=
  {r | IsRel 𝔄 r}

variable (I A) in
/-- **Tulenbaev's relative Steinberg group `St(A, 𝔄)`** (T Def 1.5), as a presented group. -/
abbrev RelSt (𝔄 : Ideal A) : Type _ :=
  PresentedGroup (rels I A 𝔄)

variable {𝔄 : Ideal A}

/-- The generator `X_{v,w}`. -/
def X (p : (I → A) × (I → A)) (hp : RMem 𝔄 p) : RelSt I A 𝔄 :=
  PresentedGroup.of (⟨p, hp⟩ : RGen I A 𝔄)

theorem X_congr {p q : (I → A) × (I → A)} (h : p = q) (hp : RMem 𝔄 p) (hq : RMem 𝔄 q) :
    X p hp = X q hq := by
  subst h
  rfl

/-- Relation (1.1). -/
theorem X_add (v w w' : I → A) (h₁ : RMem 𝔄 (v, w)) (h₂ : RMem 𝔄 (v, w'))
    (h₃ : RMem 𝔄 (v, w + w')) : X (v, w) h₁ * X (v, w') h₂ = X (v, w + w') h₃ := by
  apply eq_of_mul_inv_eq_one
  have hrel : FreeGroup.of (⟨(v, w), h₁⟩ : RGen I A 𝔄) * FreeGroup.of ⟨(v, w'), h₂⟩ *
      (FreeGroup.of ⟨(v, w + w'), h₃⟩)⁻¹ ∈ rels I A 𝔄 :=
    IsRel.add v w w' h₁ h₂ h₃
  simpa only [X, PresentedGroup.of, map_mul, map_inv] using PresentedGroup.one_of_mem hrel

#audit_axioms X_add

/-- Relation (1.2). -/
theorem X_conj (p q : (I → A) × (I → A)) (hp : RMem 𝔄 p) (hq : RMem 𝔄 q)
    (hc : RMem 𝔄 (conjPair p q)) : X p hp * X q hq * (X p hp)⁻¹ = X (conjPair p q) hc := by
  apply eq_of_mul_inv_eq_one
  have hrel : FreeGroup.of (⟨p, hp⟩ : RGen I A 𝔄) * FreeGroup.of ⟨q, hq⟩ *
      (FreeGroup.of ⟨p, hp⟩)⁻¹ * (FreeGroup.of ⟨conjPair p q, hc⟩)⁻¹ ∈ rels I A 𝔄 :=
    IsRel.conj p q hp hq hc
  simpa only [X, PresentedGroup.of, map_mul, map_inv] using PresentedGroup.one_of_mem hrel

#audit_axioms X_conj

/-- Relation (1.3). -/
theorem X_frame (v v' w u : I → A) (b : A) (hu : u ⬝ᵥ v = 0) (hu' : u ⬝ᵥ v' = 1)
    (hw : w ⬝ᵥ v = 0) (h₁ : RMem 𝔄 (b • v + v', w)) (h₂ : RMem 𝔄 (v, b • w))
    (h₃ : RMem 𝔄 (v', w)) : X (b • v + v', w) h₁ = X (v, b • w) h₂ * X (v', w) h₃ := by
  apply eq_of_mul_inv_eq_one
  have hrel : FreeGroup.of (⟨(b • v + v', w), h₁⟩ : RGen I A 𝔄) *
      (FreeGroup.of ⟨(v, b • w), h₂⟩ * FreeGroup.of ⟨(v', w), h₃⟩)⁻¹ ∈ rels I A 𝔄 :=
    IsRel.frame v v' w u b hu hu' hw h₁ h₂ h₃
  simpa only [X, PresentedGroup.of, map_mul, map_inv] using PresentedGroup.one_of_mem hrel

#audit_axioms X_frame

theorem X_zero (v : I → A) (h : RMem 𝔄 (v, 0)) : X (v, 0) h = 1 := by
  have h0 : X (v, 0) h * X (v, 0) h = X (v, 0) h := by
    rw [X_add v 0 0 h h (h.add h)]
    exact X_congr (by simp) _ _
  exact mul_left_cancel (h0.trans (mul_one _).symm)

#audit_axioms X_zero

theorem X_neg (v w : I → A) (h : RMem 𝔄 (v, w)) (h' : RMem 𝔄 (v, -w)) :
    X (v, -w) h' = (X (v, w) h)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [X_add v w (-w) h h' (h.add h'),
    X_congr (show (v, w + -w) = (v, (0 : I → A)) by simp) _ h.zero]
  exact X_zero v _

#audit_axioms X_neg

end Presentation

end RelPres
end K2Found
end BooneHigmanLinear
end GroupApproximation
