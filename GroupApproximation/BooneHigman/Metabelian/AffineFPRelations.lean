import Mathlib.Algebra.Ring.Subring.Basic
import GroupApproximation.BooneHigman.Metabelian.AffineFPIdentities

/-!
# The affine relations and steps A, B (lane bh-met-05)

Research node `affine-extension-of-fp-elementary-group-is-fp-proof`
(`research/artifacts/bh-sl3-zt-host-2026-09-12.md`, §2).  `AffineRel S x τ` records, for a
family `x i j r` of elements of a group `P` and a family `τ k`, the Steinberg relations of the
`x`, together with the finitely many affine relations of the presentation:

* (C1) `x i j ε` commutes with `τ k` for `ε ∈ S`, `k ≠ j`;
* (C2) `x i j 1 · τ j · (x i j 1)⁻¹ = τ j τ i`;
* (C3) the `τ k` pairwise commute,

where `S ∋ 1` generates the ring.  This file proves step A (`commute_x_tau`: (C1) holds for all
`r`, via the subring of good coefficients) and step B (`commute_tau_y`: every `τ l` commutes
with `⁅x i k r, τ k⁆`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace AffineFP

open scoped commutatorElement

/-- The relations of the affine presentation, for a family `x i j r` of Steinberg generators
and a family `τ k` of translation generators in a group `P`. -/
structure AffineRel {I R P : Type*} [CommRing R] [Group P] (S : Set R)
    (x : ∀ i j : I, i ≠ j → R → P) (τ : I → P) : Prop where
  add : ∀ (i j : I) (h : i ≠ j) (a b : R), x i j h (a + b) = x i j h a * x i j h b
  comm : ∀ (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → l ≠ i → ∀ a b : R,
    Commute (x i j hij a) (x k l hkl b)
  adj : ∀ (i j k : I) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
    ⁅x i j hij a, x j k hjk b⁆ = x i k hik (a * b)
  c1 : ∀ (i j : I) (h : i ≠ j) (ε : R), ε ∈ S → ∀ k : I, k ≠ j → Commute (x i j h ε) (τ k)
  c2 : ∀ (i j : I) (h : i ≠ j), x i j h 1 * τ j * (x i j h 1)⁻¹ = τ j * τ i
  c3 : ∀ k l : I, Commute (τ k) (τ l)
  one_mem : (1 : R) ∈ S
  closure : Subring.closure S = ⊤
  four : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c

namespace AffineRel

variable {I R P : Type*} [CommRing R] [Group P] {S : Set R}
  {x : ∀ i j : I, i ≠ j → R → P} {τ : I → P}

theorem x_zero (hR : AffineRel S x τ) (i j : I) (h : i ≠ j) : x i j h 0 = 1 := by
  have e := hR.add i j h 0 0
  rw [add_zero] at e
  exact mul_left_cancel (show x i j h 0 * x i j h 0 = x i j h 0 * 1 by rw [mul_one, ← e])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.x_zero

theorem x_neg (hR : AffineRel S x τ) (i j : I) (h : i ≠ j) (r : R) :
    x i j h (-r) = (x i j h r)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← hR.add, neg_add_cancel, hR.x_zero])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.x_neg

/-- Conjugation of `x i k r` by `x k l s`. -/
theorem conj_x_left (hR : AffineRel S x τ) (i k l : I) (hik : i ≠ k) (hkl : k ≠ l)
    (hil : i ≠ l) (r s : R) :
    x k l hkl s * x i k hik r * (x k l hkl s)⁻¹ = (x i l hil (r * s))⁻¹ * x i k hik r := by
  calc x k l hkl s * x i k hik r * (x k l hkl s)⁻¹
      = ⁅x i k hik r, x k l hkl s⁆⁻¹ * x i k hik r := by
        rw [commutatorElement_inv, commutatorElement_def]
        group
    _ = (x i l hil (r * s))⁻¹ * x i k hik r := by rw [hR.adj i k l hik hkl hil]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.conj_x_left

/-- Conjugation of `x i k r` by `x a i s`. -/
theorem conj_x_right (hR : AffineRel S x τ) (a i k : I) (hai : a ≠ i) (hik : i ≠ k)
    (hak : a ≠ k) (s r : R) :
    x a i hai s * x i k hik r * (x a i hai s)⁻¹ = x a k hak (s * r) * x i k hik r := by
  calc x a i hai s * x i k hik r * (x a i hai s)⁻¹
      = ⁅x a i hai s, x i k hik r⁆ * x i k hik r := by
        rw [commutatorElement_def]
        group
    _ = x a k hak (s * r) * x i k hik r := by rw [hR.adj a i k hai hik hak]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.conj_x_right

/-- The coefficients `r` for which (C1) holds at `r`. -/
def GoodCoeff (x : ∀ i j : I, i ≠ j → R → P) (τ : I → P) (r : R) : Prop :=
  ∀ (i j : I) (h : i ≠ j) (k : I), k ≠ j → Commute (x i j h r) (τ k)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.GoodCoeff

theorem goodCoeff_mul (hR : AffineRel S x τ) {a b : R} (ha : GoodCoeff x τ a)
    (hb : GoodCoeff x τ b) : GoodCoeff x τ (a * b) := by
  intro i j h k hk
  obtain ⟨l, hli, hlj, hlk⟩ := hR.four i j k
  rw [← hR.adj i l j hli.symm hlj h a b, commutatorElement_def]
  have h1 := ha i l hli.symm k hlk.symm
  have h2 := hb l j hlj k hk
  exact ((h1.mul_left h2).mul_left h1.inv_left).mul_left h2.inv_left

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.goodCoeff_mul

/-- The subring of good coefficients. -/
def goodSubring (hR : AffineRel S x τ) : Subring R where
  carrier := {r | GoodCoeff x τ r}
  mul_mem' := fun {_ _} ha hb => hR.goodCoeff_mul ha hb
  one_mem' := fun i j h k hk => hR.c1 i j h 1 hR.one_mem k hk
  add_mem' := fun {a b} ha hb i j h k hk => by
    rw [hR.add i j h a b]
    exact (ha i j h k hk).mul_left (hb i j h k hk)
  zero_mem' := fun i j h k _ => by
    rw [hR.x_zero i j h]
    exact Commute.one_left _
  neg_mem' := fun {a} ha i j h k hk => by
    rw [hR.x_neg i j h a]
    exact (ha i j h k hk).inv_left

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.goodSubring

/-- Step A: relation (C1) holds for every coefficient. -/
theorem commute_x_tau (hR : AffineRel S x τ) (r : R) (i j : I) (h : i ≠ j) (k : I)
    (hk : k ≠ j) : Commute (x i j h r) (τ k) := by
  have hS : S ⊆ (hR.goodSubring : Set R) := fun s hs i' j' h' k' hk' =>
    hR.c1 i' j' h' s hs k' hk'
  have hT : (⊤ : Subring R) ≤ hR.goodSubring := by
    rw [← hR.closure]
    exact Subring.closure_le.mpr hS
  have hr : GoodCoeff x τ r := hT (Subring.mem_top r)
  exact hr i j h k hk

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.commute_x_tau

/-- Step B: every `τ l` commutes with `⁅x i k r, τ k⁆`. -/
theorem commute_tau_y (hR : AffineRel S x τ) (i k : I) (h : i ≠ k) (r : R) (l : I) :
    Commute (τ l) ⁅x i k h r, τ k⁆ := by
  by_cases hlk : l = k
  · rw [hlk]
    obtain ⟨m, hmi, hmk, -⟩ := hR.four i k k
    exact commute_of_shear (s := τ m) (h := x k m hmk.symm 1)
      (c := (x i m hmi.symm (r * 1))⁻¹)
      (hR.commute_x_tau r i k h m hmk).symm (hR.c3 m k) (hR.c2 k m hmk.symm)
      (hR.commute_x_tau 1 k m hmk.symm k hmk.symm).mul_inv_cancel
      (hR.conj_x_left i k m h hmk.symm hmi.symm r 1)
      (hR.comm i m i k hmi.symm h hmi h.symm (r * 1) r).inv_left
      (hR.commute_x_tau (r * 1) i m hmi.symm k hmk.symm).inv_left
  · exact commute_commutator_of (hR.commute_x_tau r i k h l hlk).symm (hR.c3 l k)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.commute_tau_y

end AffineRel

end AffineFP
end Metabelian
end BooneHigman
end GroupApproximation
