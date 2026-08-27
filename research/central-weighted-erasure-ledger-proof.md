---
rg: 2
id: central-weighted-erasure-ledger-proof
kind: route
title: Clean small bad-row sets, reset exceptional blocks, and integrate Markov
target: central-weighted-erasure-ledger-recovers-reset-density
requires:
  - soundness-unique-neighbors-give-erasure-cleaning
  - all-dual-unique-neighbors-contract-operator-tails
  - block-adaptive-sparse-reset-is-cheap
---

Blockwise Markov gives

```text
sum_omega lambda_omega |E_omega|/M
 <=E_par/rho^2.                                         (CWP1)
```

Partition the blocks into `G={omega:|E_omega|<kappa L}` and its
complement.  On `G`, `(SUN4)` gives

```text
sum_G lambda_omega |S_omega|/L
 <=(M/(gamma L)) sum_G lambda_omega |E_omega|/M.
```

On the complement choose `S_omega=[L]`.  Since
`1<=|E_omega|/(kappa L)`, its total weighted density is at most

```text
(M/(kappa L)) sum_(not G) lambda_omega |E_omega|/M.
```

Combine the two bounds with `(CWP1)` and `M/L<=nu_+` to prove `(CWE4)`.
The cleaning inclusion is `(SUN4)` on `G` and tautological when
`S_omega=[L]`.

For `(CWE5)`, multiply blockwise `(AUT2)` by `lambda_omega/L`, sum, and
bound

```text
sum_omega lambda_omega b_(rho,omega)/M<=E_par/rho^2
```

again by Markov.  The exceptional blocks have already been paid by the
second part of the preceding partition.

Now `(BAS2)--(BAS3)` turn weighted coordinate density into squared
generator displacement and induced overlay energy, proving `(CWE6)`.
Repeated-original balancing assigns total normalized weight `Theta(1/M)`
to each original row, so its contribution is comparable with `E_par`.
All arguments are positive and pointwise in the central decomposition;
monotone approximation gives the direct-integral extension.

