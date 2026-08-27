---
rg: 2
id: bmg2-does-not-exclude-hyperfinite-atlas
kind: claim
title: The nonuniform BMG2 gaps do not exclude a hyperfinite Atlas coefficient algebra
invalidates:
  - atlas-nonhyperfinite-from-bmg2-rounding
distinct_from:
  leavitt-regular-atlas-block-monomial-gap: that proves a positive gap `e_R` for every fixed internal matrix-size bound `R`; this audits the reversed quantifiers needed when `R` is supplied by a hyperfinite approximation and grows with its accuracy.
  atlas-positive-coefficients-are-nonhyperfinite: that remains an open structural claim; this refutes only the tempting deduction from BMG2 plus finite-dimensional approximation and polar rounding.
  atlas-purified-witness-macroscopic-commutator: that forces positive-density noncommutativity in a fixed coefficient pair; hyperfinite factors contain such pairs, so that spectral carrier does not repair the missing approximation modulus.
---

**ESTABLISHED QUANTIFIER FIREWALL.**  Let `(U_i)` be a hypothetical positive
purified Atlas certificate and suppose, as strongly as the proposed argument
needs, that for every `eta>0` its coefficient tuple admits finite-dimensional
approximants which lift to the matrix stages and whose simple summands have
size at most `R(eta)`.  Grant also dimension-free polar rounding, so there
are relative unitaries `V_i^(eta)` with those bounded coefficient algebras
and

```text
limsup_omega ||U_i-V_i^(eta)||_2 <= C_0 eta.             (QF1)
```

Word Lipschitzness and vanishing Atlas defect of `U_i` give

```text
limsup_omega F(V_i^(eta)) <= C eta                      (QF2)
```

for a fixed packet constant `C`.  Since all coefficient weight of
`V_i^(eta)` lies in summands of size at most `R(eta)`, `(BMG2)` gives only

```text
sqrt(e_(R(eta))) <= C eta.                              (QF3)
```

There is no contradiction.  Hyperfiniteness has quantifiers

```text
for every eta>0 there exist B_eta and R(eta),
```

whereas the desired application would require

```text
there exist B and R with dist_2(coefficients,B)
                    < sqrt(e_R)/C.                     (QF4)
```

No implication from the first statement to `(QF4)` is valid without a
uniform relation between approximation accuracy and `e_R`.

The compatibility is intrinsic to the positive Atlas hypothesis.  If
`E_r` denotes the least fixed-`r` average Atlas energy used in the proof of
`(BMG2)` and `e_R=min_(r<=R)E_r`, the purified witnesses have
`r_i->infinity` and energy tending to zero.  Therefore

```text
e_(r_i) <= E_(r_i) -> 0.                               (QF5)
```

So the very hypothesis under audit already forces the available gap scale
to collapse along growing matrix sizes.  It is consistent for `R(eta)` to
grow fast enough that `(QF3)` holds at every accuracy.

This firewall grants rather than disputes finite-dimensional lifting and
polar rounding.  Those steps cannot repair the quantifiers.  The route
would become valid with an additional modulus, for example a theorem
producing approximants with

```text
C eta < sqrt(e_(R(eta))),                              (QF6)
```

or a uniform positive lower bound for the relevant `e_R`; neither follows
from hyperfiniteness or `(BMG2)`.  Consequently the possibility that the
ultraproduct coefficient algebra is hyperfinite remains open.
