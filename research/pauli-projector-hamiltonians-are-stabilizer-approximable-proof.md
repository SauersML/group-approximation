---
rg: 2
id: pauli-projector-hamiltonians-are-stabilizer-approximable-proof
kind: route
title: Rewrite a Pauli-projector sum as half the frustration of a Pauli sum and apply stabilizer rounding
target: pauli-projector-hamiltonians-are-stabilizer-approximable
requires: [pauli-sums-near-their-one-norm-round-to-stabilizer-states]
artifacts:
  - research/artifacts/pauli-frustration-stabilizer-rounding-2026-09-12.md
---

Put `K = sum_a w_a s_a P_a`, a Pauli decomposition of weight `W = sum_a w_a`.
Then `H = (W I - K)/2`, so `lambda_min(H) = (W - lambda_max(K))/2`, and every state
`phi` has `<phi|H|phi> = (W - <phi|K|phi>)/2`. By
`pauli-sums-near-their-one-norm-round-to-stabilizer-states`, some stabilizer `phi`
has `<phi|K|phi> >= lambda_max(K) - (1+sqrt2)(W - lambda_max(K))`, hence

```text
<phi|H|phi> <= (W - lambda_max(K))(2+sqrt2)/2 = (2+sqrt2) lambda_min(H).
```

**Code-space constraints.** For `Pi_a = prod_(i<=r_a)(I+g_(a,i))/2`, expanding the
product gives `2^(-r_a) sum_(S subseteq [r_a]) g_(a,S)`, where the `g_(a,S)` are
distinct signed Paulis because the generators are independent. So `Pi_a` has a
Pauli decomposition of weight exactly one, and `K = sum_a w_a Pi_a`, listing all
these terms, has weight `W = sum_a w_a`. Also `H = sum_a w_a(I-Pi_a) = W I - K`, so
`lambda_min(H) = W - lambda_max(K)` and `<phi|H|phi> = W - <phi|K|phi>`. By (SR), some
stabilizer `phi` has `<phi|H|phi> <= (W-lambda_max(K))(1+(1+sqrt2)) = (2+sqrt2)lambda_min(H)`.
The term list has `2^(r_a)` entries per constraint. That is polynomial for `r_a = O(log n)`.
For larger `r_a` the verifier instead computes `<phi|Pi_a|phi>`, which is `2^(-t)` or `0`,
by stabilizer-group intersection in polynomial time.

**NP.** A stabilizer state is described by `n` commuting independent signed
Pauli generators. Validity is checked by symplectic linear algebra over `F_2`.
For each term, `<phi|P_a|phi>` is `0` if `P_a` anticommutes with some generator,
and otherwise `+-1`, with the sign found by solving for `P_a` as a product of
generators (Aaronson--Gottesman). The energy is therefore an exact rational in
polynomial time. On YES instances some stabilizer state has energy at most
`(2+sqrt2)a < b`. On NO instances every state has energy at least `b`. The verifier
accepts iff the energy is below a rational threshold in `((2+sqrt2)a, b)`. The
Pauli-sum version is the same with (SR) and monotonicity in `lambda_max`.

**Examples.** `(I-X)/2+(I-Z)/2`, averaged, has
`lambda_min = (1-1/sqrt2)/2` while stabilizer states give at least `1/4`, ratio
`1+1/sqrt2`. Zero ground energy forces all `s_a P_a` to share a `+1` eigenvector;
they then commute, so a stabilizer ground state exists. Section 3 of the artifact.
