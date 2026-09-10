import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import GroupApproximation.CharClass.ParityPTwist

/-!
# L4a, step five: the `e`-expansion of a homogeneous symmetric polynomial

This is the crux of L4a, and after it everything else in the lemma is bookkeeping.  The
statement is

> the `e`-expansion of a symmetric polynomial that is homogeneous of degree `w` in the
> variables is **weighted**-homogeneous of weight `w`, where the `e`-variable `X_a` carries
> weight `a + 1`.

Two things follow from it, and they are the two the assembly needs.  First, `eCoeff (N−1)`
annihilates every homogeneous piece of degree `≠ N`, because the monomial `X_{N−1}` has
weight `N` and a weighted-homogeneous polynomial has no coefficient at a monomial of the
wrong weight (`MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero`).  So the weight-`N` part
of a twisted class never has to be extracted as an element — the functional isolates it.
Second, a weight-`N`-homogeneous `f` satisfies `f − eCoeff(f)·e_N ∈ IsDecomposable`, which
is the element-level membership the `wu` field of `ParityPData` wants.

This file proves the direction the crux rests on: **`esymmAlgHom` carries weighted-homogeneous
of weight `w` to homogeneous of degree `w`**, because `X_a ↦ e_{a+1}` and `e_{a+1}` is
homogeneous of degree `a+1`.  The converse — which is the crux itself — then follows from
uniqueness of the homogeneous decomposition together with injectivity of `esymmAlgHom`, and
is the one place in the whole lane where `esymmAlgEquiv`'s *surjectivity* is used rather
than its injectivity.

## What Mathlib supplies and what it does not

`Mathlib/RingTheory/MvPolynomial/Homogeneous.lean` and `.../WeightedHomogeneous.lean`
between them have `IsHomogeneous.sum`, `.prod`, `.mul`, `.pow`, `isHomogeneous_C`,
`isHomogeneous_X`, `IsWeightedHomogeneous`, `weightedHomogeneousComponent`,
`sum_weightedHomogeneousComponent`, `IsWeightedHomogeneous.coeff_eq_zero`, and an induction
principle `IsWeightedHomogeneous.induction_on` with `zero`, `add` and `monomial` cases.

The one gap: there is **no `esymm_isHomogeneous`** anywhere in
`Mathlib/RingTheory/MvPolynomial/Symmetric/`.  It is proved here, in ten lines, from
`IsHomogeneous.prod` and `isHomogeneous_X`.

## Main results

* `GroupApproximation.CharClass.ParityP.esymm_isHomogeneous` — `e_a` is homogeneous of
  degree `a`.
* `ParityP.eWeight` — the weight of the `e`-variable `X_a` is `a + 1`.
* `ParityP.isHomogeneous_esymmAeval` — `esymmAlgHom` carries weight to degree.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

namespace ParityP

open MvPolynomial

section Homog

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **`e_a` is homogeneous of degree `a`.**  Not in Mathlib at the pin. -/
theorem esymm_isHomogeneous (a : ℕ) :
    MvPolynomial.IsHomogeneous (esymm (Fin n) R a) a := by
  rw [MvPolynomial.esymm]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun B hB => ?_
  have hcard : B.card = a := (Finset.mem_powersetCard.mp hB).2
  have h1 : MvPolynomial.IsHomogeneous
      (∏ i ∈ B, (X i : MvPolynomial (Fin n) R)) (∑ _i ∈ B, 1) :=
    MvPolynomial.IsHomogeneous.prod B _ (fun _ => 1) fun i _ => isHomogeneous_X R i
  simpa [hcard] using h1

/-- The weight carried by the `e`-variable `X a`, namely `a + 1`, since `X a` stands for
`e_{a+1}` under `esymmAlgHom`. -/
def eWeight (n : ℕ) : Fin n → ℕ := fun a => (a : ℕ) + 1

@[simp] theorem eWeight_apply (a : Fin n) : eWeight n a = (a : ℕ) + 1 := rfl

/-- **The direction the crux rests on.**  The substitution `X_a ↦ e_{a+1}` carries a
polynomial that is weighted-homogeneous of weight `w` to one that is homogeneous of degree
`w`.  Proved by the weighted-homogeneous induction principle; the only case with content is
the monomial one, where the degree is `∑_a (a+1)·d a`, which is the weight of `d`. -/
theorem isHomogeneous_esymmAeval {w : ℕ} {F : MvPolynomial (Fin n) R}
    (hF : MvPolynomial.IsWeightedHomogeneous (eWeight n) F w) :
    MvPolynomial.IsHomogeneous
      (aeval (fun i : Fin n => esymm (Fin n) R ((i : ℕ) + 1)) F) w := by
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
    rw [map_zero]
    exact MvPolynomial.isHomogeneous_zero _ _ _
  | add p q hp hq ihp ihq =>
    rw [map_add]
    exact ihp.add ihq
  | monomial d r hr =>
    rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
    have hprod : MvPolynomial.IsHomogeneous
        (d.prod fun i k => (esymm (Fin n) R ((i : ℕ) + 1)) ^ k)
          (∑ i ∈ d.support, ((i : ℕ) + 1) * d i) := by
      refine MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => ?_
      exact (esymm_isHomogeneous ((i : ℕ) + 1)).pow (d i)
    have hw : (∑ i ∈ d.support, ((i : ℕ) + 1) * d i) = w := by
      rw [← hr, Finsupp.weight_apply, Finsupp.sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [eWeight_apply, smul_eq_mul, Nat.mul_comm]
    rw [← hw]
    simpa using (MvPolynomial.isHomogeneous_C (σ := Fin n) r).mul hprod

end Homog

end ParityP

end GroupApproximation.CharClass
