---
rg: 2
id: atlas-full-coefficient-automorphism-twists-are-gauge
kind: claim
title: Full-coefficient automorphism twists are commutant gauge or conjugate duplicates
invalidates:
  - atlas-full-coefficient-noninner-twist-model
distinct_from:
  atlas-full-relator-data-factor-through-double-commutant-gauge: that proves invariance under already implemented left and right chart-commutant unitaries; this classifies every multiplicative star-preserving automorphism of a full growing coefficient block and shows that it supplies no additional noninner operation.
  atlas-equal-block-flattening-is-commutant-gauge: that shows a particular block-flattening construction is gauge; this rules out the entire simultaneous full-coefficient automorphism ansatz, including conjugate-linear twists.
  atlas-a4-19243-classical-collapse: that audits inner and outer automorphisms of the finite A8 label chart; this concerns automorphisms of the multiplicity coefficient algebra and explicitly does not remove the A8 outer-marking branch.
---

**ESTABLISHED SCOPED NO-GO.**  Let `A=A8`, let `lambda` be its real left
regular representation, and let

```text
U in U(l2(A) tensor C^r),
U=(U_xy)_(x,y in A),
C*(U_xy)=M_r(C).                                      (FCA1)
```

Let `alpha:M_r(C)->M_r(C)` be a unital real-linear, multiplicative,
star-preserving bijection, and apply it simultaneously to all coefficient
blocks:

```text
U^alpha=(alpha(U_xy))_(x,y in A).                     (FCA2)
```

Then one of the following holds.

1. There is `V in U(r)` such that

   ```text
   U^alpha=(I tensor V) U (I tensor V)^*.             (FCA3)
   ```

2. There is `V in U(r)` such that

   ```text
   U^alpha=(I tensor V) conjugate(U) (I tensor V)^*.  (FCA4)
   ```

Consequently every literal two-chart word `w` has exactly the same
normalized-Hilbert--Schmidt defect at `U^alpha` as at `U` (in the second
case, the word value is the conjugate of the old value up to one fixed
unitary conjugacy):

```text
||pi_(U^alpha)(w)-I||_2=||pi_U(w)-I||_2.              (FCA5)
```

The same remains true after taking any direct sum of automorphism-twisted
copies of `U`: every summand has the same defect for each named word, so the
normalized squared defect of the sum is unchanged.  Hence mixing inner and
conjugate-linear twists cannot lower the objective either.

Thus a simultaneous "outer," semilinear, or field twist of the purified
full matrix coefficient block cannot create a positive Atlas model from a
failed one.  In the complex-linear case it is already in the relative
double-commutant gauge orbit; in the conjugate-linear case it is merely the
complex-conjugate duplicate.

This does **not** rule out genuinely operator-valued positive-density
constructions.  A survivor must couple different block positions by data
which is not one automorphism of `M_r(C)`--for example a nonstationary family
of mixed compressions--and must separately verify the global block-unitary
and Atlas word equations.  Nor does the statement concern the noninner
automorphism of the finite label group `A8`, which acts on the `l2(A8)`
coordinate rather than on `M_r(C)`.

DERIVATION
atlas-full-coefficient-automorphism-gauge-proof
