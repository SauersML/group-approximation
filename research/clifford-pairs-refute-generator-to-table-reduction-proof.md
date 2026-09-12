---
rg: 2
id: clifford-pairs-refute-generator-to-table-reduction-proof
kind: route
title: Compute the cocycle of independent Clifford pairs
target: averaged-commutators-do-not-give-abelian-table
requires: []
---

On `(C^2)^(tensor m)`, let

```text
A_(2k-1)=X_k,                 A_(2k)=Z_k.
```

Different tensor factors commute, and each pair `(X_k,Z_k)` anticommutes.
There are `2m` offending ordered generator pairs, each of squared normalized
HS commutator norm `4`.  Since `L^2=4m^2`, this proves `(SGC1)`.

For `a in F_2^(2m)`, use the fixed ordered section

```text
phi(a)=prod_(k=1)^m X_k^(a_(2k-1)) Z_k^(a_(2k)).          (CPT1)
```

Collecting two such words gives the exact cocycle formula

```text
phi(a)phi(b)=(-1)^S phi(a+b),
S=sum_(k=1)^m a_(2k)b_(2k-1) mod 2.                      (CPT2)
```

For independent uniform `a,b`, the summands in `S` are independent
Bernoulli variables of parameter `1/4`.  Therefore

```text
Pr[S=1]=(1-(1-2/4)^m)/2=(1-2^(-m))/2.                   (CPT3)
```

The squared normalized HS distance between a unitary and its negative is
`4`.  Equations `(CPT2)`--`(CPT3)` give `(SGC2)`.  Hence the vanishing
quantity `(SGC1)` cannot control the full-table defect needed by the cited
uniform abelian rounding theorem.
