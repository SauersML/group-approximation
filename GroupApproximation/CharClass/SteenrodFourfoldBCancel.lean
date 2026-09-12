import GroupApproximation.CharClass.SteenrodFourfoldBDecomp

/-!
# The characteristic-two cancellation

Differentiating the second composite produces four families of terms indexed by
the splitting of the resolution index.  Two of them are the same family read at a
shift of one: the term the left block contributes at index `p + 1` is the term
the right block contributes at index `p`.  Since the left block contributes
nothing at index `0`, the two sums are equal, and in characteristic two equal
means they cancel.

That is the whole of the cancellation, and it is about sums rather than about
diagonals, so it is stated and proved here for an arbitrary family in an
arbitrary module of characteristic two.

## Main results

* `add_self_zmod2` — characteristic two, for any `ZMod 2`-module.
* `sum_shift_cancel` — **two families that coincide after a shift, one of which
  starts at zero, sum to zero.**
-/

namespace GroupApproximation
namespace CharClass
namespace Steenrod

/-- Any module over `ZMod 2` has characteristic two. -/
theorem add_self_zmod2 {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from by decide, zero_smul]

/-- **The cancellation.**  If the second family is the first read one step
later, and the first vanishes at `0`, the two sums cancel.

This is the shape the computation produces: the left block of the Leibniz rule
contributes at index `p + 1` exactly what the right block contributes at index
`p`, and contributes nothing at index `0` because there is no boundary to take
in degree zero. -/
theorem sum_shift_cancel {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (n : ℕ) (A B : ℕ → M) (h : ∀ p, A (p + 1) = B p) (h0 : A 0 = 0) :
    (∑ p ∈ Finset.range (n + 1), A p) + (∑ p ∈ Finset.range n, B p) = 0 := by
  rw [Finset.sum_range_succ', h0, add_zero,
    Finset.sum_congr rfl (fun p (_ : p ∈ Finset.range n) => h p)]
  exact add_self_zmod2 _

end Steenrod
end CharClass
end GroupApproximation
