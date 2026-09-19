---
rg: 2
id: kleene-mipco-self-destroying-game
kind: claim
title: The coRE game compiler has a fixed point separating commuting and finite-dimensional value
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
  - GroupApproximation/Quantum/FiniteMeasurement.lean
distinct_from:
  perfect-lcs-gap-implies-nonhyperlinear: that is a group consequence of a perfect LCS gap; this is a self-referential construction of one general nonlocal game gap and performs no groupification.
  robust-locally-satisfiable-relator-code: that asks for normalized-HS group-word soundness plus sparse local satisfiability; this remains entirely at the nonlocal-game level.
---

Let the effective constant-gap orientation of `MIP^co=coRE` assign a finite
game `V_M` and universal constants `c>s` so that

```text
M does not halt  =>  omega_co(V_M) >= c,
M halts          =>  omega_co(V_M) <= s.                            (KMG1)
```

For every computable `theta` with `s<theta<c`, there is an effectively
specified game `V_*` satisfying

```text
omega_co(V_*) >= c > theta >= omega_*(V_*).                         (KMG2)
```

Here `omega_*` is the supremum over finite-dimensional tensor-product
strategies.  The construction is literal self-reference: its fixed-point
machine computes its own game and enumerates finite-dimensional strategies,
halting as soon as it certifies value greater than `theta`.

Lin, arXiv:2510.07162, proves `MIP^co=coRE` using recursive compression and
tracially embeddable strategies.  The claim above is the recursion-theorem
consequence of the resulting effective constant-gap compiler, not a claim that
the paper has already converted the game into a finitely presented group.
