---
rg: 2
id: kleene-halting-mark-collapse-diagonal
kind: claim
title: Halting-side mark survival and nonhalting-side microstate collapse self-instantiate to a nonhyperlinear group
artifacts:
  - research/artifacts/fanizza-native-signal-diagonal-2026-08-20.md
distinct_from:
  kleene-self-destroying-microstate-lemma: that assumes nonhalting-side word survival and halting-side collapse and diagonalizes against a microstate search; this uses the reverse compiler orientation and diagonalizes against enumeration of a proof that the marked word is trivial.
  self-referential-bcs-nonzero-signal-collapse: that performs the same logical orientation inside a finitely presented star-algebra; this proves the group-level statement needed for hyperlinearity.
---

Suppose there is a total computable map from Turing-machine indices `e` to a
finite presentation, a marked word, and computable rationals

```text
(Gamma_e=<S_e|R_e>,w_e,delta_e,alpha_e),
delta_e>0,                 0<=alpha_e<sqrt(2),                    (KHC1)
```

such that

```text
machine e halts     => w_e!=1 in Gamma_e,                         (KHC2)

machine e does not halt
  => Def_(R_e)(U)<delta_e implies
     ||w_e(U)-I||_2<=alpha_e                                    (KHC3)
```

for every finite-dimensional unitary tuple `U`.  Then one can effectively
specify a finite presentation of a nonhyperlinear group.

Unlike the usual microstate-search diagonal, `(KHC1)` need not use constants
uniform in `e`.  In particular the soundness modulus may be any positive
computable function of the finite presentation produced from `e`; it need
not be uniform in a machine runtime which is not known to halt.
