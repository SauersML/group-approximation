---
rg: 2
id: centralized-clause-affine-quotient-proof
kind: route
title: Test the central clause quotient by its faithful regular trace
target: centralized-clause-zero-face-is-exact-affine-bcs-quotient
requires:
  - centralized-gram-row-words-upgrade-trace-gap-to-vector-gap
---

If `phi(D)=0`, positivity of the summands gives

```text
pi_phi(u_i) xi_phi=xi_phi
```

for every `i`. Since each `u_i` is central, it fixes the dense cyclic set
`pi_phi(Gamma)xi_phi`; hence it is the identity in the GNS representation.
The representation factors through `barGamma`. Therefore `(CZQ3)` implies
item 1.

Conversely, pull the canonical regular trace of `barGamma` back to
`C*(Gamma)`. It is tracial, every `u_i` is one, and hence `D` has zero
expectation. Item 1 gives

```text
0=tau_barGamma(H_B)
 =sum_(R in R_B) ||R(bar z)||_(2,L(barGamma))^2.
```

Faithfulness of the regular trace gives `(CZQ3)` term by term. This proves
the equivalence, including the version restricted to decoded-tracial states.

The involution and within-context commutator residuals in `(CZQ3)` make
`A_c` an elementary abelian two-group. Its group algebra decomposes as the
direct sum of the character idempotents

```text
p_a=2^(-|U_c|) product_(x in U_c)(1+a_x bar z_x),
```

with repetitions identified exactly by the relations among the generators.
An assignment idempotent is nonzero precisely when the assignment descends
to a character of `A_c`. These descending assignments are the annihilator
of the relation subspace among the `bar z_x`, proving `(CZQ5)`. The forbidden
projection residuals vanish precisely when none of their assignments
descends, proving `(CZQ6)`.

Finally, let `rho` be the perfect representation in the claim. If
`b in N intersect B`, then `rho(b)=1` because every clause is killed, while
faithfulness of the scalar `B`-character gives `rho(b)!=1` for `b!=1`.
Thus `b=1`, proving `(CZQ7)`.
