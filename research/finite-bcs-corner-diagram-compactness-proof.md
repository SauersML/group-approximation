---
rg: 2
id: finite-bcs-corner-diagram-compactness-proof
kind: route
title: Collect finite word-equality witnesses for the corner diagram
target: finite-bcs-corner-diagram-is-finitely-witnessed
requires: []
---

Expand every expression in `(FDC1)` as a finite complex linear combination
of words in the free group `F(X)`.  There are only finitely many resulting
expressions and each has finite support.

For one such expression

```text
z=sum_(k=1)^n c_k w_k,
```

the assertion `z=0` in `C[Gamma]` says that, in every equivalence class for
equality in `Gamma`, the sum of the coefficients of the `w_k` in that class
is zero.  For each class meeting this finite support, choose one representative
word and, for every other word in the class, choose a proof

```text
w_k w_rep^(-1) in <<R>>.
```

Membership in a normal closure is finitary: each chosen proof is a finite
product of conjugates of relators from `R` and their inverses.  Collect the
finitely many relators used by all these proofs, for all expressions in
`(FDC1)`, and collect all generator letters appearing in the relevant words,
relators, and conjugators.  Call the resulting finite sets `R_0` and `X_0`.
Then words that were equal inside each relevant `Gamma`-class are already
equal in `Gamma_0=<X_0|R_0>`.  Words from distinct `Gamma`-classes cannot
become equal in `Gamma_0`, because the natural homomorphism
`Gamma_0 -> Gamma` would carry such an equality to `Gamma`.  Thus the
coefficient partition for every displayed expression is exactly the same in
`Gamma_0`, and all identities `(FDC1)` hold there.

It remains to check the strict condition `q!=0`.  More generally, the
partition of the finite support of `q` into equality classes in `Gamma_0`
refines its partition in `Gamma`.  If every aggregate coefficient of `q`
vanished in `C[Gamma_0]`, summing those zero aggregates over the finer blocks
would make every aggregate vanish in `C[Gamma]`, contrary to the hypothesis.
Hence `q!=0` already in `C[Gamma_0]`.

The projection, corner-unit, star, and the finitely many defining relations
of `B` now give `(FDC2)`.  If `B` has no CE tracial state,
`nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear` applied to
`Gamma_0` shows directly that this finite stage is nonhyperlinear.
