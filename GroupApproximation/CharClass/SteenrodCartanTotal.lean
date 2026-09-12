import GroupApproximation.CharClass.SteenrodTotal

/-!
# The Cartan formula, transported to the total ring

`cc-wu`'s `ParityData.cartanH` and `cc-projective`'s `SqData.cartan` both want
the Cartan formula as a statement about the **ungraded** ring `TotalH X`, with
the sum over `Finset.range (n+1)` and the second index written `n - i`:

```text
SqH X n (u * v) = ∑ i ∈ Finset.range (n+1), SqH X i u * SqH X (n-i) v
```

`cc-cartan` will supply the **graded** formula, one bidegree at a time.  This
file is the bridge, and it is written now, with the graded formula as a
hypothesis, so that the moment `cc-cartan` lands theirs the consumers' field is
one application away rather than a fresh proof.

## Why the hypothesis is stated the way it is

The naive graded statement `Sq n (cup a b) = ∑ i, cup (Sq i a) (Sq (n-i) b)` does
not typecheck: the left side has degree `n + (p + q)` and the `i`-th right-hand
term has degree `(i + p) + ((n - i) + q)`, equal only propositionally and only
when `i ≤ n`.  Pushing both sides into `TotalH` removes the obstruction, because
`TotalH.of` absorbs the degree and the ring multiplication does the bookkeeping.
So `CartanOf` below is the graded formula in cast-free form; converting a
`cohCast`-laden graded statement into it is one rewrite with `TotalH.of_mul` and
`of_cohCast`.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

variable {X : TopCat.{0}}

/-- **The graded Cartan formula, cast-free.**  This is what `cc-cartan` has to
deliver; everything else in this file is bookkeeping on top of it. -/
def CartanOf (X : TopCat.{0}) : Prop :=
  ∀ (n p q : ℕ) (a : Hmod2 X p) (b : Hmod2 X q),
    TotalH.of X (n + (p + q)) (Sq n (cup a b))
      = ∑ i ∈ Finset.range (n + 1),
          TotalH.of X (i + p) (Sq i a) * TotalH.of X ((n - i) + q) (Sq (n - i) b)

/-- **The Cartan formula on the total ring**, in exactly the shape of `cc-wu`'s
`ParityData.cartanH` and `cc-projective`'s `SqData.cartan`.  Both sides are
biadditive, so the graded formula on a pair of homogeneous classes propagates
over the direct sum. -/
theorem SqH_mul_of_cartanOf (hcart : CartanOf X) (n : ℕ) (u v : TotalH X) :
    SqH X n (u * v) = ∑ i ∈ Finset.range (n + 1), SqH X i u * SqH X (n - i) v := by
  induction u using DirectSum.induction_on with
  | zero => simp
  | of p a =>
      induction v using DirectSum.induction_on with
      | zero => simp
      | of q b =>
          show SqH X n (TotalH.of X p a * TotalH.of X q b)
            = ∑ i ∈ Finset.range (n + 1),
                SqH X i (TotalH.of X p a) * SqH X (n - i) (TotalH.of X q b)
          rw [← TotalH.of_mul, SqH_of]
          simp only [SqH_of]
          exact hcart n p q a b
      | add v₁ v₂ hv₁ hv₂ =>
          simp only [mul_add, map_add, hv₁, hv₂, Finset.sum_add_distrib]
  | add u₁ u₂ hu₁ hu₂ =>
      simp only [add_mul, map_add, hu₁, hu₂, Finset.sum_add_distrib]

end

end Steenrod
end CharClass
end GroupApproximation
