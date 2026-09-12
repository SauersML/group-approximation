import GroupApproximation.CharClass.OddPTuple

/-!
# How the Koszul prefix moves when one slot is differentiated

The whole content of `d ∘ d = 0` for the flat tuple model is two facts about
`tupPre`, and this file is them.  Isolating them is deliberate: the square-zero
proof is a double sum split into a diagonal and two off-diagonal halves, and if
the sign bookkeeping is inlined there it is impossible to see which half is
which.

**Differentiating slot `j` does not move the prefix at any slot `≤ j`, and drops
it by exactly one at every slot `> j`.**  That asymmetry is the cancellation:
differentiating `a` then `b` with `a < b` picks up `(-1)^{P_a + P_b - 1}`,
because the second prefix has already dropped; doing `b` then `a` picks up
`(-1)^{P_a + P_b}`, because differentiating a *later* slot leaves an earlier
prefix alone.  The two differ by a sign and cancel.

At `p = 2` this is invisible: `CartanFreeCx`'s corresponding step says "the two
mixed terms are equal and cancel because two is zero", which is a different
mechanism that happens to reach the same conclusion.  Anyone porting that proof
by changing the coefficient ring gets a false theorem.
-/

namespace GroupApproximation.CharClass

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

variable {X : TopCat.{0}} {r : ℕ}

/-- Updating slot `j` leaves the prefix at every slot `l ≤ j` alone, because that
prefix sums over slots strictly below `l`, none of which is `j`. -/
theorem tupPre_update_of_le (t : Fin r → TagSimp X) (j : Fin r) (τ : TagSimp X)
    (l : Fin r) (h : l ≤ j) :
    tupPre (Function.update t j τ) l = tupPre t l := by
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmj : m ≠ j := by
    have : m < l := Finset.mem_Iio.mp hm
    exact ne_of_lt (lt_of_lt_of_le this h)
  rw [Function.update_of_ne hmj]

/-- Updating slot `j` by a tag of degree one lower drops the prefix at every slot
`l > j` by exactly one. -/
theorem tupPre_update_of_lt (t : Fin r → TagSimp X) (j : Fin r) (τ : TagSimp X)
    (l : Fin r) (h : j < l) (hd : τ.1 + 1 = (t j).1) :
    tupPre (Function.update t j τ) l + 1 = tupPre t l := by
  have hj : j ∈ Finset.Iio l := Finset.mem_Iio.mpr h
  have hrest : ∀ m ∈ (Finset.Iio l).erase j,
      (Function.update t j τ m).1 = (t m).1 := by
    intro m hm
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]
  -- `Finset.add_sum_erase` reads `f a + ∑ erase = ∑ s`, so splitting a sum off
  -- is the BACKWARD rewrite.  Forward, it hunts for a pattern that is on the
  -- other side of the goal and higher-order unification does not find it.
  have e1 : tupPre (Function.update t j τ) l
      = τ.1 + ∑ m ∈ (Finset.Iio l).erase j, (t m).1 := by
    rw [tupPre, ← Finset.add_sum_erase _ _ hj, Function.update_self]
    exact congrArg (fun z => τ.1 + z) (Finset.sum_congr rfl hrest)
  have e2 : tupPre t l = (t j).1 + ∑ m ∈ (Finset.Iio l).erase j, (t m).1 := by
    rw [tupPre]
    exact (Finset.add_sum_erase _ _ hj).symm
  omega

/-- **The cancellation, as an identity of signs.**  With `a < b`, differentiating
`a` then `b` and differentiating `b` then `a` accumulate opposite signs. -/
theorem tupPre_sign_cancel {K : Type} [CommRing K] (t : Fin r → TagSimp X)
    (a b : Fin r) (σ : TagSimp X) (hab : a < b)
    (hσ : σ.1 + 1 = (t a).1) :
    ((-1 : K) ^ tupPre t a) * ((-1 : K) ^ tupPre (Function.update t a σ) b)
      + ((-1 : K) ^ tupPre t b) * ((-1 : K) ^ tupPre t a) = 0 := by
  have hb : tupPre (Function.update t a σ) b + 1 = tupPre t b :=
    tupPre_update_of_lt t a σ b hab hσ
  have hrw : tupPre t b = tupPre (Function.update t a σ) b + 1 := hb.symm
  rw [hrw, pow_succ]
  ring

end GroupApproximation.CharClass
