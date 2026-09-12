import GroupApproximation.Sofic.SoficAction
import GroupApproximation.Sofic.SoficIntegerExtension

/-!
# The cyclic stack of a twisted model

Section 12 of the ascending-HNN dossier.  Soficity of an action is stable under
adjoining a compatible cyclic normalizer, and the model witnessing this stacks
`L` twisted copies of a model for the normal part around a cycle of length `L`.

This file isolates the permutation algebra of that stack, independently of any
charts:

* `twistedShift` is the permutation `(j, a) ↦ (j + q, f (j + q) a)` of the stack
  `ZMod L × A`;
* `stackPerm` specialises it to the semidirect product `N ⋊[φ] ℤ`, sending
  `n t�q` to the stack permutation which shifts the level by `q` and acts on the
  fibre through the level-twisted label `φ⁻ʲ(n)`;
* `stackPerm_apply_eq_of_not_bad` is the exact agreement statement: away from
  the `O(|q|)` wrap-around levels of `badLevels`, the stack permutation of a
  product agrees with the product of the stack permutations as soon as the
  underlying model is multiplicative on the two twisted labels involved.

The wrap-around bookkeeping (`badLevels`, `val_add_of_not_bad`,
`card_badLevels_le`) is reused verbatim from the group-level construction in
`Sofic.SoficIntegerExtension`.
-/

namespace GroupApproximation
namespace CyclicStack

open SemidirectProduct

universe u v

/-! ## Twisted shifts of a cyclic stack -/

variable {A : Type v} (L : ℕ)

/-- The permutation of the cyclic stack `ZMod L × A` which shifts the level by
`q` and then acts on the fibre by the level-dependent permutation `f`. -/
def twistedShift (q : ℤ) (f : ZMod L → Equiv.Perm A) : Equiv.Perm (ZMod L × A) where
  toFun p := (p.1 + (q : ZMod L), f (p.1 + (q : ZMod L)) p.2)
  invFun p := (p.1 - (q : ZMod L), (f p.1).symm p.2)
  left_inv := by
    intro p
    simp
  right_inv := by
    intro p
    have h : p.1 - (q : ZMod L) + (q : ZMod L) = p.1 := by ring
    simp [h]

@[simp] theorem twistedShift_apply (q : ℤ) (f : ZMod L → Equiv.Perm A)
    (p : ZMod L × A) :
    twistedShift L q f p = (p.1 + (q : ZMod L), f (p.1 + (q : ZMod L)) p.2) :=
  rfl

theorem twistedShift_zero_one : twistedShift L 0 (fun _ => (1 : Equiv.Perm A)) = 1 := by
  refine Equiv.ext fun p => ?_
  simp

/-! ## The stack permutation of a semidirect product -/

variable {N : Type u} [Group N] (φ : Multiplicative ℤ →* MulAut N)

/-- The stack permutation attached to an element of `N ⋊[φ] ℤ` and a model
`ψ` of `N`.  Level `j` carries the label twisted by `φ` to depth `j`. -/
noncomputable def stackPerm (ψ : N → Equiv.Perm A)
    (g : N ⋊[φ] Multiplicative ℤ) : Equiv.Perm (ZMod L × A) :=
  twistedShift L (Multiplicative.toAdd g.right)
    fun j => ψ (SoficIntegerExtension.tw φ (-(j.val : ℤ)) g.left)

theorem stackPerm_one (ψ : N → Equiv.Perm A) (hψ : ψ 1 = 1) :
    stackPerm L φ ψ 1 = 1 := by
  refine Equiv.ext fun p => ?_
  have hleft : (1 : N ⋊[φ] Multiplicative ℤ).left = 1 := rfl
  have hright : Multiplicative.toAdd (1 : N ⋊[φ] Multiplicative ℤ).right = 0 := rfl
  simp only [stackPerm, twistedShift_apply, hleft, hright, Int.cast_zero, add_zero,
    SoficIntegerExtension.tw, map_one, hψ]
  rfl

/-- **Exact agreement off the wrap-around boundary.**  If the level `j` avoids
the two boundary sets attached to `h` and to `g * h`, then the stack permutation
of the product agrees with the product of the stack permutations at every fibre
point where the underlying model is multiplicative on the two twisted labels. -/
theorem stackPerm_apply_eq_of_not_bad [NeZero L] (ψ : N → Equiv.Perm A)
    (g h : N ⋊[φ] Multiplicative ℤ) (j : ZMod L) (a : A)
    (hbad1 : j ∉ SoficIntegerExtension.badLevels L (Multiplicative.toAdd h.right))
    (hbad2 : j ∉ SoficIntegerExtension.badLevels L
      (Multiplicative.toAdd g.right + Multiplicative.toAdd h.right))
    (hmulψ : ψ (SoficIntegerExtension.tw φ
          (-(((j.val : ℤ) + (Multiplicative.toAdd g.right
            + Multiplicative.toAdd h.right)))) g.left *
        SoficIntegerExtension.tw φ
          (-(((j.val : ℤ) + Multiplicative.toAdd h.right))) h.left) a
      = ψ (SoficIntegerExtension.tw φ
          (-(((j.val : ℤ) + (Multiplicative.toAdd g.right
            + Multiplicative.toAdd h.right)))) g.left)
          (ψ (SoficIntegerExtension.tw φ
            (-(((j.val : ℤ) + Multiplicative.toAdd h.right))) h.left) a)) :
    stackPerm L φ ψ (g * h) (j, a)
      = (stackPerm L φ ψ g * stackPerm L φ ψ h) (j, a) := by
  classical
  set q : ℤ := Multiplicative.toAdd g.right with hq
  set p : ℤ := Multiplicative.toAdd h.right with hp
  have hval1 : ((j + (p : ZMod L)).val : ℤ) = (j.val : ℤ) + p :=
    SoficIntegerExtension.val_add_of_not_bad hbad1
  have hval2 : ((j + ((q + p : ℤ) : ZMod L)).val : ℤ) = (j.val : ℤ) + (q + p) :=
    SoficIntegerExtension.val_add_of_not_bad hbad2
  have hrightmul : Multiplicative.toAdd (g * h).right = q + p := rfl
  have hleftmul : (g * h).left = g.left * (φ g.right) h.left := rfl
  have hfirst : j + (p : ZMod L) + (q : ZMod L) = j + ((q + p : ℤ) : ZMod L) := by
    push_cast
    ring
  have htwtw : SoficIntegerExtension.tw φ (-((j.val : ℤ) + (q + p)))
        ((φ g.right) h.left)
      = SoficIntegerExtension.tw φ (-((j.val : ℤ) + p)) h.left := by
    have hg : (φ g.right) h.left = SoficIntegerExtension.tw φ q h.left := rfl
    rw [hg, ← SoficIntegerExtension.tw_add]
    congr 1
    ring
  simp only [stackPerm, twistedShift_apply, Equiv.Perm.mul_apply, hrightmul,
    hleftmul, ← hq, ← hp, hfirst, hval1, hval2, Prod.mk.injEq]
  rw [SoficIntegerExtension.tw_mul, htwtw]
  exact ⟨trivial, hmulψ⟩


/-! ## Composition and the fibrewise density estimate -/

/-- Twisted shifts compose to twisted shifts. -/
theorem twistedShift_mul (q r : ℤ) (f f' : ZMod L → Equiv.Perm A) :
    twistedShift L q f * twistedShift L r f'
      = twistedShift L (q + r) (fun k => f k * f' (k - (q : ZMod L))) := by
  refine Equiv.ext fun p => ?_
  have hlevel : p.1 + (r : ZMod L) + (q : ZMod L) = p.1 + ((q + r : ℤ) : ZMod L) := by
    push_cast; ring
  have hfib : p.1 + ((q + r : ℤ) : ZMod L) - (q : ZMod L) = p.1 + (r : ZMod L) := by
    push_cast; ring
  simp only [Equiv.Perm.mul_apply, twistedShift_apply, hlevel, hfib]

variable [Fintype A] [DecidableEq A]

theorem permDist_le_one (p q : Equiv.Perm A) : permDist p q ≤ 1 := by
  classical
  by_cases hA : Fintype.card A = 0
  · simp [permDist, hA]
  · have hpos : (0 : ℝ) < (Fintype.card A : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hA
    rw [permDist, div_le_one hpos]
    have hle := Finset.card_filter_le (Finset.univ : Finset A) (fun a => p a ≠ q a)
    rw [Finset.card_univ] at hle
    exact_mod_cast hle

/-- **Fibrewise average.**  Two twisted shifts with the same shift are at the
average of their fibrewise distances. -/
theorem permDist_twistedShift [NeZero L] (q : ℤ) (f f' : ZMod L → Equiv.Perm A) :
    permDist (twistedShift L q f) (twistedShift L q f')
      = (∑ k : ZMod L, permDist (f k) (f' k)) / L := by
  classical
  have hne_iff : ∀ p : ZMod L × A,
      (twistedShift L q f p ≠ twistedShift L q f' p)
        ↔ f (p.1 + (q : ZMod L)) p.2 ≠ f' (p.1 + (q : ZMod L)) p.2 := by
    intro p
    simp [twistedShift_apply, Prod.ext_iff]
  set D : Finset (ZMod L × A) :=
    Finset.univ.filter fun p => twistedShift L q f p ≠ twistedShift L q f' p with hD
  have hfiber : ∀ k : ZMod L,
      D.filter (fun p => p.1 + (q : ZMod L) = k)
        = ({k - (q : ZMod L)} : Finset (ZMod L)) ×ˢ
            (Finset.univ.filter fun a : A => f k a ≠ f' k a) := by
    intro k
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpD, hk⟩ := hp
      rw [hD, Finset.mem_filter] at hpD
      have h2 := (hne_iff p).mp hpD.2
      rw [hk] at h2
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · simp only [Finset.mem_singleton]
        rw [← hk]; ring
      · simp [h2]
    · intro hp
      rw [Finset.mem_product] at hp
      have h1 : p.1 = k - (q : ZMod L) := by simpa using hp.1
      have h2 : f k p.2 ≠ f' k p.2 := by simpa using hp.2
      have hk : p.1 + (q : ZMod L) = k := by rw [h1]; ring
      refine Finset.mem_filter.mpr ⟨?_, hk⟩
      rw [hD, Finset.mem_filter]
      refine ⟨Finset.mem_univ p, (hne_iff p).mpr ?_⟩
      rw [hk]; exact h2
  have hcard : D.card
      = ∑ k : ZMod L, (Finset.univ.filter fun a : A => f k a ≠ f' k a).card := by
    have hsum := Finset.card_eq_sum_card_fiberwise
      (f := fun p : ZMod L × A => p.1 + (q : ZMod L)) (s := D)
      (t := (Finset.univ : Finset (ZMod L))) (fun p _ => Finset.mem_univ _)
    rw [hsum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hfiber k, Finset.card_product, Finset.card_singleton, one_mul]
  have hcardType : (Fintype.card (ZMod L × A) : ℝ)
      = (L : ℝ) * (Fintype.card A : ℝ) := by
    rw [Fintype.card_prod, ZMod.card]
    push_cast
    ring
  have hRHS : (∑ k : ZMod L, permDist (f k) (f' k)) / (L : ℝ)
      = (∑ k : ZMod L, ((Finset.univ.filter fun a : A => f k a ≠ f' k a).card : ℝ))
          / ((Fintype.card A : ℝ) * (L : ℝ)) := by
    simp only [permDist]
    rw [← Finset.sum_div, div_div]
  rw [permDist, ← hD, hcard, hcardType, hRHS, Nat.cast_sum,
    mul_comm (L : ℝ) (Fintype.card A : ℝ)]

/-- **The density estimate.**  Away from a small set of bad levels the fibrewise
distances are at most `δ`, so the stacked distance is at most
`|bad| / L + δ`. -/
theorem permDist_twistedShift_le [NeZero L] (q : ℤ) (f f' : ZMod L → Equiv.Perm A)
    (bad : Finset (ZMod L)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ k ∉ bad, permDist (f k) (f' k) ≤ δ) (hL : 0 < L) :
    permDist (twistedShift L q f) (twistedShift L q f')
      ≤ (bad.card : ℝ) / L + δ := by
  classical
  rw [permDist_twistedShift]
  have hsplit : ∑ k : ZMod L, permDist (f k) (f' k)
      ≤ (bad.card : ℝ) + (L : ℝ) * δ := by
    have hbound : ∀ k : ZMod L,
        permDist (f k) (f' k) ≤ (if k ∈ bad then (1 : ℝ) else 0) + δ := by
      intro k
      by_cases hk : k ∈ bad
      · simp only [hk, if_true]
        exact le_trans (permDist_le_one _ _) (by linarith)
      · simp only [hk, if_false, zero_add]
        exact hgood k hk
    calc ∑ k : ZMod L, permDist (f k) (f' k)
        ≤ ∑ k : ZMod L, ((if k ∈ bad then (1 : ℝ) else 0) + δ) :=
          Finset.sum_le_sum fun k _ => hbound k
      _ = (bad.card : ℝ) + (L : ℝ) * δ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_mem]
          simp [ZMod.card, mul_comm]
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  rw [div_le_iff₀ hLpos]
  calc ∑ k : ZMod L, permDist (f k) (f' k)
      ≤ (bad.card : ℝ) + (L : ℝ) * δ := hsplit
    _ = ((bad.card : ℝ) / L + δ) * L := by field_simp

end CyclicStack
end GroupApproximation
