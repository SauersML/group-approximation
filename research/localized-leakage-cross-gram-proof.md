---
rg: 2
id: localized-leakage-cross-gram-proof
kind: route
title: Combine the localized non-CE gap with two-branch capacity
target: localized-non-ce-leakage-forces-cross-gram-overlap
requires:
  - corner-localized-non-ce-bcs-energy-gap
  - gram-branching-capacity-with-overlap
---

Apply the localized BCS gap to each leakage projection `L_i`.  With the
notation of `(NCL1)--(NCL5)` this gives

```text
Lambda_i >= beta_B^corner tau(L_i),
ell <= Lambda/beta_B^corner.                            (LLG1)
```

Apply the two-branch Gram-capacity inequality with capacity projection `C`
and branches `T_1,T_2`.  Because `C` commutes with the exit projections,
its leakage term is `ell`; the ordered cross-Gram sum is

```text
||T_1^*T_2||_2^2 + ||T_2^*T_1||_2^2 = 2 Theta.
```

Thus `(GBC2)` reads

```text
c >= s-2ell-2Theta,
Theta >= (s-c)/2-ell.                                  (LLG2)
```

Substituting `(LLG1)` proves

```text
Theta >= (s-c)/2 - Lambda/beta_B^corner,
```

which is `(NCL6)`.  If
`Lambda < beta_B^corner(s-c)/4`, then `(LLG1)--(LLG2)` give
`Theta>(s-c)/4`, proving `(NCL7)`.  The proof uses the mixed leakage moments,
so it retains the matrix-only/non-CE asymmetry and makes no universal
tracial positivity assertion.
