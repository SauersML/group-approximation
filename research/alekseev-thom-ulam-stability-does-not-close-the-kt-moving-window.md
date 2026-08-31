---
rg: 2
id: alekseev-thom-ulam-stability-does-not-close-the-kt-moving-window
kind: claim
title: Hyperfinite Ulam stability does not close the Kun--Thom moving window
artifacts:
  - research/pointwise-lamp-microstates-fail-the-uniform-ball-and-leave-multiplicity-proof.md
distinct_from:
  kt-cyclic-parity-is-an-exact-quasiregular-return-correspondence: That identifies the pointed return which must be controlled; this proves that Ulam rounding of the lamp algebra neither supplies the required hypothesis globally nor controls the return multiplicity after rounding.
---

**ESTABLISHED APPLICABILITY FENCE; THE KT ROOT REMAINS OPEN.**

(Source: arXiv:2606.07369.)

Alekseev--Thom, arXiv:2606.07369, Theorem 3.5 is dimension-free in
matrix size, but its input is a map

~~~text
phi:M_N(C)_(<=1) -> M_(<=1)
~~~

which is uniformly approximately additive, homogeneous, multiplicative,
star-preserving, and unital on the **entire operator-norm unit ball**.
The conclusion is a uniformly close genuine homomorphism after a small
semifinite amplification.

A Kun--Thom group microstate does not supply this input.

1. The binary finite lamp window is
   `C[(C_2)^F]=C^(2^|F|)`, not a full matrix algebra. It contains no
   off-diagonal matrix units to which the matrix theorem could be applied.

2. On every fixed window one can include all lamp words and all of their
   multiplication rows and round that finite abelian algebra. This is only
   fixed-window exactification. A group microstate gives pointwise
   convergence for each fixed word pair, not one map on the unit ball of the
   infinite hyperfinite lamp algebra with a uniform defect.

3. This quantifier gap is real even inside the hyperfinite factor. If
   `R=tensor_(j>=1) M_2`, `A_n=tensor_(j<=n)M_2`, and
   `E_n:R->A_n` is the trace-preserving conditional expectation, then

~~~text
||E_n(xy)-E_n(x)E_n(y)||_2 -> 0                          (KUS1)
~~~

for every fixed `x,y in R`, while

~~~text
sup_(||x||,||y||<=1)
 ||E_n(xy)-E_n(x)E_n(y)||_2 =1                           (KUS2)
~~~

for every `n`. Thus pointwise moving-window control cannot be fed into
the Ulam theorem for `R`.

The bilateral version is also pointwise covariant for the exact tensor
shift: centered finite-window expectations asymptotically commute with every
fixed shift on every fixed element, while their uniform multiplicative
defect remains one. Actor covariance does not repair the quantifier order.

Even granting a nonabelian Pauli enrichment and the full uniform hypothesis
on a finite factor does not close the route. After Ulam rounding, an exact
embedding has the form

~~~text
theta(M_N)=M_N tensor 1  subset  M_N tensor K.
~~~

Every unitary implementing a prescribed automorphism of the matrix factor
has the exact normal form

~~~text
U=theta(w) V,             V in theta(M_N)'.              (KUS3)
~~~

The factor `V` is an arbitrary unitary on the multiplicity algebra. Lamp
rounding controls `theta(w)` and leaves `V` completely untouched. Actor
multiplication and property-(T) constraints on the family of such `V`'s
are exactly the original Kun--Thom multiplicity-cocycle problem.

For the named cyclic parity, fixed-window rounding actually preserves the
canonical separation from its `h=e_12(x_2/x_1)` translate; it does not
force the commutator to shrink. A valid bridge would require either:

- uniform-on-the-unit-ball approximate crossed-product structure, including
  the multiplicity commutant and actor covariance; or
- a new pointed theorem controlling the specific norm-one
  quasi-regular vector without such a uniform lift.

Neither follows from arXiv:2606.07369. The global route remains **OPEN**.

DERIVATION
pointwise-lamp-microstates-fail-the-uniform-ball-and-leave-multiplicity-proof
