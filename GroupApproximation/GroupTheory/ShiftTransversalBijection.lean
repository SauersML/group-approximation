import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Finite.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Tactic.Group

/-!
# `θ`, `κ` and `ζ`: the shift of a finite window of a finite group

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602, section "LEF groups", tex l.367–377:

> Let ψ map the ball of radius 2r of Γ injectively into a finite group Q, preserving the products that stay in it, and let
> θ, with θ(v)_{−3r} = 1 and θ(v)_m = v_{m−1} otherwise, be the isomorphism from {v ∈ Q^{[−3r,3r]} : v_{3r−1} = v_{3r}} onto
> {v ∈ Q^{[−3r,3r]} : v_{−3r} = 1}. Transversals give a bijection κ of Q^{[−3r,3r]} with κ(vx) = θ(v)κ(x) for v in the domain
> of θ. Let each v ∈ Q^{[−3r,3r]} act on Q^{[−3r,3r]} × ℤ/5r by left multiplication on the first coordinate, and put
> ζ(x,i) = (κ(x), i+1), so that ζvζ⁻¹ = θ(v) on the domain of θ.

The window `[−3r, 3r]` is `Fin (M + 2)` (with `M + 2 = 6r + 1` in the application), position `k` standing for the level
`k − 3r`. Position `0` is the level `−3r`, and the last two positions are the levels `3r − 1` and `3r`.

* `dom` and `ran`, the two subgroups;
* `theta`: the homomorphism `v ↦ Fin.cons 1 (v ∘ castSucc)`, with `theta_injOn` and `theta_surjOn` (the isomorphism of the
  domain onto the range);
* `kappa`: built from right complements of `dom` and `ran`, which have the same cardinality, with `kappa_mul_left`;
* `lmul` and `zeta`, with `zeta_mul_lmul_mul_zeta_inv`: `ζ v ζ⁻¹ = θ(v)` for `v ∈ dom`.
-/

namespace GroupApproximation
namespace ShiftTransversalBijection

open Equiv Subgroup

section Theta

variable (Q : Type*) [Group Q] (M : ℕ)

/-- `{v : v_{3r−1} = v_{3r}}`, the domain of `θ` (tex l.370). -/
def dom : Subgroup (Fin (M + 2) → Q) where
  carrier := {v | v (Fin.castSucc (Fin.last M)) = v (Fin.last (M + 1))}
  mul_mem' {a b} ha hb := by
    show (a * b) (Fin.castSucc (Fin.last M)) = (a * b) (Fin.last (M + 1))
    have ha' : a (Fin.castSucc (Fin.last M)) = a (Fin.last (M + 1)) := ha
    have hb' : b (Fin.castSucc (Fin.last M)) = b (Fin.last (M + 1)) := hb
    simp only [Pi.mul_apply, ha', hb']
  one_mem' := by
    show (1 : Fin (M + 2) → Q) (Fin.castSucc (Fin.last M)) = (1 : Fin (M + 2) → Q) (Fin.last (M + 1))
    rfl
  inv_mem' {a} ha := by
    show a⁻¹ (Fin.castSucc (Fin.last M)) = a⁻¹ (Fin.last (M + 1))
    have ha' : a (Fin.castSucc (Fin.last M)) = a (Fin.last (M + 1)) := ha
    simp only [Pi.inv_apply, ha']

theorem mem_dom {v : Fin (M + 2) → Q} :
    v ∈ dom Q M ↔ v (Fin.castSucc (Fin.last M)) = v (Fin.last (M + 1)) :=
  Iff.rfl

/-- `{v : v_{−3r} = 1}`, the range of `θ` (tex l.370–371). -/
def ran : Subgroup (Fin (M + 2) → Q) where
  carrier := {v | v 0 = 1}
  mul_mem' {a b} ha hb := by
    show (a * b) 0 = 1
    have ha' : a 0 = 1 := ha
    have hb' : b 0 = 1 := hb
    simp only [Pi.mul_apply, ha', hb', one_mul]
  one_mem' := by
    show (1 : Fin (M + 2) → Q) 0 = 1
    rfl
  inv_mem' {a} ha := by
    show a⁻¹ 0 = 1
    have ha' : a 0 = 1 := ha
    simp only [Pi.inv_apply, ha', inv_one]

theorem mem_ran {v : Fin (M + 2) → Q} : v ∈ ran Q M ↔ v 0 = 1 :=
  Iff.rfl

/-- **`θ`**: `θ(v)_{−3r} = 1` and `θ(v)_m = v_{m−1}` otherwise (tex l.369). -/
def theta : (Fin (M + 2) → Q) →* (Fin (M + 2) → Q) where
  toFun v := Fin.cons 1 fun k : Fin (M + 1) => v (Fin.castSucc k)
  map_one' := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ k => simp
  map_mul' v w := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ k => simp

@[simp] theorem theta_zero (v : Fin (M + 2) → Q) : theta Q M v 0 = 1 :=
  Fin.cons_zero _ _

@[simp] theorem theta_succ (v : Fin (M + 2) → Q) (k : Fin (M + 1)) :
    theta Q M v k.succ = v (Fin.castSucc k) :=
  Fin.cons_succ _ _ _

theorem theta_mem_ran (v : Fin (M + 2) → Q) : theta Q M v ∈ ran Q M :=
  theta_zero Q M v

/-- `θ` is injective on its domain. -/
theorem theta_injOn {v w : Fin (M + 2) → Q} (hv : v ∈ dom Q M) (hw : w ∈ dom Q M)
    (h : theta Q M v = theta Q M w) : v = w := by
  have hc : ∀ k : Fin (M + 1), v (Fin.castSucc k) = w (Fin.castSucc k) := fun k => by
    rw [← theta_succ Q M v k, ← theta_succ Q M w k, h]
  funext i
  induction i using Fin.lastCases with
  | last =>
    rw [mem_dom] at hv hw
    rw [← hv, ← hw, hc]
  | cast k => exact hc k

/-- `θ` maps its domain onto its range. -/
theorem theta_surjOn {u : Fin (M + 2) → Q} (hu : u ∈ ran Q M) : ∃ v ∈ dom Q M, theta Q M v = u := by
  refine ⟨Fin.lastCases (motive := fun _ => Q) (u (Fin.last (M + 1))) (fun j : Fin (M + 1) => u j.succ), ?_, ?_⟩
  · rw [mem_dom, Fin.lastCases_last, Fin.lastCases_castSucc, Fin.succ_last]
  · funext i
    induction i using Fin.cases with
    | zero =>
      rw [theta_zero]
      exact hu.symm
    | succ k => rw [theta_succ, Fin.lastCases_castSucc]

end Theta

section Kappa

variable (Q : Type*) [Group Q] [Finite Q] (M : ℕ)

/-- A right complement of `dom`. -/
noncomputable def domComplement : Set (Fin (M + 2) → Q) :=
  (exists_isComplement_right (dom Q M) 1).choose

theorem isComplement_dom : IsComplement (dom Q M : Set (Fin (M + 2) → Q)) (domComplement Q M) :=
  (exists_isComplement_right (dom Q M) 1).choose_spec.1

/-- A right complement of `ran`. -/
noncomputable def ranComplement : Set (Fin (M + 2) → Q) :=
  (exists_isComplement_right (ran Q M) 1).choose

theorem isComplement_ran : IsComplement (ran Q M : Set (Fin (M + 2) → Q)) (ranComplement Q M) :=
  (exists_isComplement_right (ran Q M) 1).choose_spec.1

omit [Finite Q] in
theorem card_dom_eq_card_ran : Nat.card (dom Q M) = Nat.card (ran Q M) :=
  Nat.card_congr (Equiv.ofBijective
    (fun v : dom Q M => (⟨theta Q M v, theta_mem_ran Q M v⟩ : ran Q M))
    ⟨fun v w h => Subtype.ext (theta_injOn Q M v.2 w.2 (congrArg Subtype.val h)),
     fun u => by
      obtain ⟨v, hv, hvu⟩ := theta_surjOn Q M u.2
      exact ⟨⟨v, hv⟩, Subtype.ext hvu⟩⟩)

/-- **Transversals** (tex l.371): the two complements have the same cardinality. -/
theorem card_complement_eq : Nat.card (domComplement Q M) = Nat.card (ranComplement Q M) := by
  have h1 := (isComplement_dom Q M).card_mul_card
  have h2 := (isComplement_ran Q M).card_mul_card
  have hc : Nat.card ↥(dom Q M : Set (Fin (M + 2) → Q)) = Nat.card ↥(ran Q M : Set (Fin (M + 2) → Q)) :=
    card_dom_eq_card_ran Q M
  haveI : Nonempty ↥(ran Q M : Set (Fin (M + 2) → Q)) := ⟨⟨1, (ran Q M).one_mem⟩⟩
  rw [hc] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)

/-- A bijection between the two complements. -/
noncomputable def complementEquiv : domComplement Q M ≃ ranComplement Q M :=
  Classical.choice (Finite.card_eq.1 (card_complement_eq Q M))

/-- `κ(x) = θ(d) t'` for `x = d t` with `d ∈ dom`, `t` in the complement, and `t'` its partner. -/
noncomputable def kappaFun (x : Fin (M + 2) → Q) : Fin (M + 2) → Q :=
  theta Q M ((isComplement_dom Q M).equiv x).1 *
    (complementEquiv Q M ((isComplement_dom Q M).equiv x).2 : Fin (M + 2) → Q)

theorem kappaFun_mul_left {v : Fin (M + 2) → Q} (hv : v ∈ dom Q M) (x : Fin (M + 2) → Q) :
    kappaFun Q M (v * x) = theta Q M v * kappaFun Q M x := by
  rw [kappaFun, kappaFun, IsComplement.equiv_mul_left_of_mem (isComplement_dom Q M) hv]
  simp only [Subgroup.coe_mul, map_mul, mul_assoc]

theorem kappaFun_injective : Function.Injective (kappaFun Q M) := by
  intro x y h
  have h' := (isComplement_ran Q M).1
    (a₁ := (⟨theta Q M ((isComplement_dom Q M).equiv x).1, theta_mem_ran Q M _⟩,
      complementEquiv Q M ((isComplement_dom Q M).equiv x).2))
    (a₂ := (⟨theta Q M ((isComplement_dom Q M).equiv y).1, theta_mem_ran Q M _⟩,
      complementEquiv Q M ((isComplement_dom Q M).equiv y).2)) h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h'
  have hfst : ((isComplement_dom Q M).equiv x).1 = ((isComplement_dom Q M).equiv y).1 :=
    Subtype.ext (theta_injOn Q M ((isComplement_dom Q M).equiv x).1.2
      ((isComplement_dom Q M).equiv y).1.2 (congrArg Subtype.val h1))
  have hsnd : ((isComplement_dom Q M).equiv x).2 = ((isComplement_dom Q M).equiv y).2 :=
    (complementEquiv Q M).injective h2
  exact (isComplement_dom Q M).equiv.injective (Prod.ext hfst hsnd)

/-- **`κ`**, the bijection of the window with `κ(vx) = θ(v)κ(x)` for `v ∈ dom` (tex l.371–373). -/
noncomputable def kappa : Perm (Fin (M + 2) → Q) :=
  Equiv.ofBijective (kappaFun Q M) (Finite.injective_iff_bijective.1 (kappaFun_injective Q M))

theorem kappa_apply (x : Fin (M + 2) → Q) : kappa Q M x = kappaFun Q M x :=
  rfl

theorem kappa_mul_left {v : Fin (M + 2) → Q} (hv : v ∈ dom Q M) (x : Fin (M + 2) → Q) :
    kappa Q M (v * x) = theta Q M v * kappa Q M x :=
  kappaFun_mul_left Q M hv x

variable (L : ℕ)

/-- Left multiplication on the first coordinate of `Q^{[−3r,3r]} × ℤ/L` (tex l.373–375). -/
def lmul : (Fin (M + 2) → Q) →* Perm ((Fin (M + 2) → Q) × ZMod L) where
  toFun v := Equiv.prodCongr (Equiv.mulLeft v) (Equiv.refl _)
  map_one' := Equiv.ext fun z => Prod.ext (one_mul z.1) rfl
  map_mul' v w := Equiv.ext fun z => Prod.ext (mul_assoc v w z.1) rfl

omit [Finite Q] in
theorem lmul_apply (v : Fin (M + 2) → Q) (z : (Fin (M + 2) → Q) × ZMod L) :
    lmul Q M L v z = (v * z.1, z.2) :=
  rfl

/-- **`ζ(x, i) = (κ(x), i + 1)`** (tex l.375–376). -/
noncomputable def zeta : Perm ((Fin (M + 2) → Q) × ZMod L) :=
  Equiv.prodCongr (kappa Q M) (Equiv.addRight 1)

theorem zeta_apply (z : (Fin (M + 2) → Q) × ZMod L) : zeta Q M L z = (kappa Q M z.1, z.2 + 1) :=
  rfl

/-- **`ζ v ζ⁻¹ = θ(v)` on the domain of `θ`** (tex l.376–377). -/
theorem zeta_mul_lmul_mul_zeta_inv {v : Fin (M + 2) → Q} (hv : v ∈ dom Q M) :
    zeta Q M L * lmul Q M L v * (zeta Q M L)⁻¹ = lmul Q M L (theta Q M v) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine Equiv.ext fun z => Prod.ext ?_ rfl
  simp only [Perm.mul_apply, zeta_apply, lmul_apply, kappa_mul_left Q M hv]

theorem zeta_inv_mul_lmul_theta_mul_zeta {v : Fin (M + 2) → Q} (hv : v ∈ dom Q M) :
    (zeta Q M L)⁻¹ * lmul Q M L (theta Q M v) * zeta Q M L = lmul Q M L v := by
  rw [← zeta_mul_lmul_mul_zeta_inv Q M L hv]
  group

end Kappa

end ShiftTransversalBijection
end GroupApproximation
