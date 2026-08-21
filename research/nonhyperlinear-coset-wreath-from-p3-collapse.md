---
rg: 2
id: nonhyperlinear-coset-wreath-from-p3-collapse
kind: route
title: The p = 3 collapse makes the explicit coset Bernoulli wreath group over SL3(Z[1/3]) non-hyperlinear
target: non-hyperlinear-group
requires:
  - sl3-p3-pair-relative-commutant-collapse
  - coset-bernoulli-ce-refutes-relative-commutant-collapse
---

Take

```text
Lambda = SL_3(Z),   Gamma = SL_3(Z[1/3]),
W_3 = ( direct_sum_(Gamma/Lambda) C_2 ) rtimes Gamma,      (CW3)
```

the permutational wreath product over the coset space, a finitely
generated group with `L(W_3) = L^infinity({-1,1}^(Gamma/Lambda))
rtimes Gamma`.  If `W_3` were hyperlinear, `L(W_3)` would embed in a
matrix ultraproduct; the canonical copy of `Gamma` has the regular
trace, and the lamp at the base coset commutes with `pi(Lambda)` and
is moved by `pi(h)`, `h = diag(3, 1, 1/3)`, so
`pi(Lambda)' cap M != pi(Gamma)' cap M`, contradicting
`sl3-p3-pair-relative-commutant-collapse`.  Hence `W_3` is
non-hyperlinear, which is the goal.

This edge needs no HNN carrier and no Britton reduction: the
commutant unitary is the base lamp itself.  It is the SL_3, p = 3
instance of `nonhyperlinear-coset-wreath-from-commutant-collapse`,
chosen because the candidate metaplectic flux is nontrivial at p = 3.
The subgroup-exact outlier stratum is empty
(`subgroup-exact-outliers-do-not-exist`), but the Lambda-exact spread
sector is not closed: fixed-shift invariance alone does not force a
flat profile.

**The summit in one sentence.**  Either `W_3` is non-hyperlinear --
the goal -- or `SL_3(Z)` admits regular-trace microstates that are
uniformly far from the genuine representations of EVERY finite-index
subgroup and carry the coset-Bernoulli coupling (a base lamp moved
by `h`); there is no third possibility.  The hyperlinear side of the
dichotomy is the Hayes--Sale-type soficity question for permutational
wreath products with a NON-amenable (Kazhdan) stabilizer, where the
known sofic-stabilizer theorems do not apply.
