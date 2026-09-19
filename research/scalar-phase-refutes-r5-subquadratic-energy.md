---
rg: 2
id: scalar-phase-refutes-r5-subquadratic-energy
kind: claim
title: A scalar phase on the Bleak--Quick three-cycle refutes subquadratic Carmichael energy
invalidates:
  - r5-subquadratic-energy-from-hodge-operator-bound
  - thompson-v-one-word-ceiling-from-subquadratic-energy
distinct_from:
  carmichael-energy-uniform-criteria-incomparable: That compares two abstract packet criteria using exact finite permutation matrices; this is an arbitrarily small-defect model of the actual Bleak--Quick presentation in which every conjugate of the marked generator is forced to coincide.
  affine-clone-model-defeats-pure-thompson-prefix-error-spreading: That uses growing-dimensional exact local packets; this countermodel is one-dimensional, uses the fixed finite presentation directly, and has arbitrarily small positive defect.
  subquadratic-carmichael-energy-collapse: That implication is correct once subquadratic packets exist; this disproves the proposed universal compiler supplying those packets from R1--R5.
---

**ESTABLISHED REFUTATION.**  In the three-generator Bleak--Quick
prefix-permutation presentation, the order-three element

```text
b=(01 10 11)
```

is literally one of the presentation generators; in particular `b^3` is
one of the R1 relators.  Let `R` be the finite relator set.  For real `t`,
define a one-dimensional unitary tuple by

```text
U_t(b)=z=exp(it),              U_t(x)=1  (x in X\{b}). (SPR1)
```

If `sigma_b(r)` is the exponent sum of `b` in a relator word `r`, then

```text
r(U_t)=z^(sigma_b(r)),
def_R(U_t)
 =max_(r in R)|z^(sigma_b(r))-1|
 <=L|t|,                                                   (SPR2)
```

where `L=max_(r in R)|sigma_b(r)|<infinity`.  Thus these are models of
arbitrarily small presentation defect.  The estimate is in normalized
Hilbert--Schmidt norm: for every scalar `lambda I_d`,

```text
||lambda I_d||_(2,d)=|lambda|.                            (SPR3)
```

Now fix a nonzero sufficiently small `t` with `z^4!=1`.  Every evaluated
word `U_t(g)` is scalar.  Therefore every allowed conjugate in
`r5-subquadratic-carmichael-energy` is exactly

```text
X_i=U_t(g_i)^* U_t(b) U_t(g_i)=z                         (SPR4)
```

for every choice and every length of the conjugating words.  Consequently

```text
E_M
 =sum_(i<j)||(X_iX_j)^2-1||_2^2
 =binom(M,2)|z^4-1|^2.                                  (SPR5)
```

Hence

```text
E_M/M^2 -> |z^4-1|^2/2>0,                               (SPR6)
```

along every unbounded sequence.  The asserted `o_U(M^2)` conclusion is
false no matter how the words `g_i` are chosen.

The same example directly refutes the proposed Hodge bound

```text
E_M<=C M def_R(U_t)^2:
```

for fixed `t` its right side is linear in `M`, whereas `(SPR5)` is
quadratic.  This does not affect `subquadratic-carmichael-energy-collapse`,
which remains a correct conditional matrix theorem, nor the separate
uniform-per-edge Carmichael compiler.  It kills only the claim that every
small-defect Bleak--Quick model supplies a subquadratic aggregate packet and
the square-function route proposed to prove it.

DERIVATION
scalar-phase-r5-energy-counterexample-proof
