import Mathlib.GroupTheory.CoprodI

/-!
# Alternating products in a free product

The variant Adian--Rabin construction recorded in
`Computability.RabinConstruction` reduces the whole embedding half to
retractions except for one statement about a free product: an *alternating*
product of nontrivial elements taken from distinct factors is nontrivial, and
has infinite order.

Mathlib supplies the normal form (`Monoid.CoprodI.Word.equiv`, whose inverse is
`Word.prod`) and the inductive description of nonempty reduced words
(`Monoid.CoprodI.NeWord`), but no consequence about orders.  This file is that
consequence, and it is three steps:

* `neWord_prod_ne_one` --- a nonempty reduced word is not the identity.  This is
  the normal form: `Word.prod` is injective because it is the inverse half of
  `Word.equiv`, and `NeWord.toWord` is not `empty` because its list is not nil.
* `alt` --- the reduced word spelling `(xy)ⁿ⁺¹` when `x` and `y` are nontrivial
  and lie in distinct factors.  Alternation is what makes it reduced, and it is
  the only thing being checked.
* `zpow_of_mul_of_ne_one` and `commutator_of_ne_one` --- the two forms the
  construction consumes: `of x * of y` has infinite order, and `⁅of x, of y⁆`
  is nontrivial.
-/

namespace GroupApproximation
namespace FreeProductOrder

open Monoid Monoid.CoprodI

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, Group (M i)]
  [∀ i, DecidableEq (M i)]

/-- **A nonempty reduced word is not the identity.**  `Word.prod` is injective,
being the inverse half of the normal-form equivalence, and the word of a
`NeWord` is not the empty word. -/
theorem neWord_prod_ne_one {i j : ι} (w : NeWord M i j) : w.prod ≠ 1 := by
  intro h
  have hprod : Word.prod w.toWord = 1 := by
    rw [← NeWord.prod]
    exact h
  have hinj : Function.Injective (Word.prod : Word M → CoprodI M) :=
    Word.equiv.symm.injective
  have hempty : w.toWord = Word.empty := by
    apply hinj
    rw [hprod, Word.prod_empty]
  have hnil : w.toList = List.nil := by
    have : w.toWord.toList = (Word.empty : Word M).toList := by rw [hempty]
    simpa [NeWord.toWord] using this
  exact w.toList_ne_nil hnil

/-- The reduced word spelling `(x y)ⁿ⁺¹`, for nontrivial `x`, `y` in distinct
factors. -/
def alt {i j : ι} {x : M i} {y : M j} (hx : x ≠ 1) (hy : y ≠ 1) (hij : i ≠ j) :
    ℕ → NeWord M i j
  | 0 => (NeWord.singleton x hx).append hij (NeWord.singleton y hy)
  | n + 1 => (alt hx hy hij n).append hij.symm (alt hx hy hij 0)

omit [DecidableEq ι] [∀ i, DecidableEq (M i)] in
theorem alt_prod {i j : ι} {x : M i} {y : M j} (hx : x ≠ 1) (hy : y ≠ 1)
    (hij : i ≠ j) :
    ∀ n : ℕ, (alt hx hy hij n).prod = (CoprodI.of x * CoprodI.of y) ^ (n + 1)
  | 0 => by
      simp [alt]
  | n + 1 => by
      rw [alt, NeWord.append_prod, alt_prod hx hy hij n, alt_prod hx hy hij 0,
        pow_one, ← pow_succ]

/-- **An alternating product of two nontrivial elements has infinite order.** -/
theorem pow_of_mul_of_ne_one {i j : ι} {x : M i} {y : M j} (hx : x ≠ 1)
    (hy : y ≠ 1) (hij : i ≠ j) (n : ℕ) :
    (CoprodI.of x * CoprodI.of y) ^ (n + 1) ≠ 1 := by
  rw [← alt_prod hx hy hij n]
  exact neWord_prod_ne_one _

/-- **The commutator of two nontrivial elements of distinct factors is
nontrivial.**  This is the fact the variant construction needs of
`[w, s₀]`: it vanishes exactly when `w` does. -/
theorem commutator_of_ne_one {i j : ι} {x : M i} {y : M j} (hx : x ≠ 1)
    (hy : y ≠ 1) (hij : i ≠ j) :
    CoprodI.of x * CoprodI.of y * (CoprodI.of x)⁻¹ * (CoprodI.of y)⁻¹ ≠ 1 := by
  have hxi : x⁻¹ ≠ 1 := inv_ne_one.2 hx
  have hyi : y⁻¹ ≠ 1 := inv_ne_one.2 hy
  have hw : (((NeWord.singleton x hx).append hij (NeWord.singleton y hy)).append
      hij.symm ((NeWord.singleton x⁻¹ hxi).append hij
        (NeWord.singleton y⁻¹ hyi))).prod
      = CoprodI.of x * CoprodI.of y * (CoprodI.of x)⁻¹ * (CoprodI.of y)⁻¹ := by
    simp [NeWord.append_prod, mul_assoc]
  rw [← hw]
  exact neWord_prod_ne_one _

/-! ## The commutator has infinite order

The last layer of the variant construction adjoins a stable letter along
`⟨z⟩ ≅ ⟨c⟩` with `z = ⁅w, s⁆`, so `z` must generate an infinite cyclic
subgroup, not merely be nontrivial.  The word spelling `z ⁿ⁺¹` alternates
between the two factors exactly as `alt` does, so the same argument applies. -/

/-- The reduced word spelling `⁅x, y⁆ⁿ⁺¹`. -/
def altComm {i j : ι} {x : M i} {y : M j} (hx : x ≠ 1) (hy : y ≠ 1) (hij : i ≠ j)
    (hxi : x⁻¹ ≠ 1) (hyi : y⁻¹ ≠ 1) : ℕ → NeWord M i j
  | 0 =>
      ((NeWord.singleton x hx).append hij (NeWord.singleton y hy)).append hij.symm
        ((NeWord.singleton x⁻¹ hxi).append hij (NeWord.singleton y⁻¹ hyi))
  | n + 1 =>
      (altComm hx hy hij hxi hyi n).append hij.symm (altComm hx hy hij hxi hyi 0)

omit [DecidableEq ι] [∀ i, DecidableEq (M i)] in
theorem altComm_prod {i j : ι} {x : M i} {y : M j} (hx : x ≠ 1) (hy : y ≠ 1)
    (hij : i ≠ j) (hxi : x⁻¹ ≠ 1) (hyi : y⁻¹ ≠ 1) :
    ∀ n : ℕ, (altComm hx hy hij hxi hyi n).prod
      = (CoprodI.of x * CoprodI.of y * (CoprodI.of x)⁻¹ * (CoprodI.of y)⁻¹) ^ (n + 1)
  | 0 => by
      simp [altComm, mul_assoc]
  | n + 1 => by
      rw [altComm, NeWord.append_prod, altComm_prod hx hy hij hxi hyi n,
        altComm_prod hx hy hij hxi hyi 0, pow_one, ← pow_succ]

/-- **The commutator of two nontrivial elements of distinct factors has infinite
order.**  With `w ≠ 1` this is what makes `⟨⁅w, s⁆⟩` an infinite cyclic
associated subgroup, so the last layer of the variant construction is a
legitimate HNN extension. -/
theorem pow_commutator_ne_one {i j : ι} {x : M i} {y : M j} (hx : x ≠ 1)
    (hy : y ≠ 1) (hij : i ≠ j) (n : ℕ) :
    (CoprodI.of x * CoprodI.of y * (CoprodI.of x)⁻¹ * (CoprodI.of y)⁻¹) ^ (n + 1)
      ≠ 1 := by
  have hxi : x⁻¹ ≠ 1 := inv_ne_one.2 hx
  have hyi : y⁻¹ ≠ 1 := inv_ne_one.2 hy
  rw [← altComm_prod hx hy hij hxi hyi n]
  exact neWord_prod_ne_one _

/-! ## Transferring this to the binary free product

The variant construction's base is `Monoid.Coprod Γ ℤ`, and `Monoid.Coprod` is
not defined as a `Monoid.CoprodI` --- it is its own `Con` quotient --- so the
results above do not apply to it directly.  They should not need to: all of
them say "this element is not `1`", which any homomorphism reflects, so a map
`Monoid.Coprod Γ K →* CoprodI (Bool-indexed family)` built by
`Monoid.Coprod.lift` from the two `CoprodI.of`s ought to transfer them in three
lines.

That transfer is *not* here, and the reason is worth recording because it is
not mathematical.  It has since been measured: raising `maxHeartbeats` to
1000000 and `synthInstance.maxHeartbeats` to 400000 does *not* make it go
through, so the cost is not linear in the budget --- it is blowup, and the
budget is the wrong knob.  The two-element family has to be given by recursion on
`Bool`, and it does not reduce at a variable index, so the `Group` and
`DecidableEq` instances on the factors must be supplied by hand.  Every way of
doing that which was tried --- `cond`, `Bool.rec`, an instance by cases, and
pinning the decidability instances with `letI` rather than `classical` ---
elaborates the final application into a `whnf` or `isDefEq` timeout at the
default heartbeat budget.  The obstruction is the cost of unifying
`CoprodI (pairFam Γ K)` against the instance arguments, not anything about the
statement.

Until it is done, the infinite order of the witness is a hypothesis of the
tower (`RabinVariantTower.Full` takes it as `hz`), which is where it belongs
anyway: the tower is stated for any element of infinite order, and this file
supplies the reason the witness is one. -/

end FreeProductOrder
end GroupApproximation
