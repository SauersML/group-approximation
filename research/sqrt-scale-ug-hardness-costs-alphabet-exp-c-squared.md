---
rg: 2
id: sqrt-scale-ug-hardness-costs-alphabet-exp-c-squared
kind: claim
title: If Gap-UG_k[1-eta, 1-C sqrt(eta)] is NP-hard and C > 2A sqrt(log k) then NP <= RP, so sqrt-scale ratio C needs log k >= C^2/4A^2
distinct_from:
  cmm-unique-games-sqrt-log-k-rounding: that is the CMM rounding algorithm itself; this is its consequence for the sqrt-scale quantifier level, a lower bound on the alphabet as a function of the deficit ratio C.
  sqrt-scale-unique-games-hardness-is-equivalent-to-ugc: that shows the sqrt-scale hypothesis is equivalent to UGC; this prices one instance of the hypothesis in alphabet size.
---

**ESTABLISHED.** Let `A` be the absolute constant of
`cmm-unique-games-sqrt-log-k-rounding` (natural logarithm, `k >= 2`). Suppose
that for some `k`, `eta` in `(0,1)` and `C > 2A sqrt(log k)`, the problem
`Gap-UG_k[1-eta, 1-C sqrt(eta)]` is NP-hard under Karp reductions. Then
`NP <= RP`.

Equivalently, unless `NP <= RP`, every NP-hard instance of the sqrt-scale gap
at ratio `C` has

```text
k  >=  exp( C^2 / (4 A^2) ).
```

So the hypothesis `sqrt-scale-unique-games-hardness` needs alphabets growing
like `exp(Omega(C^2))`. With `C^2 ~ ln(1/eps)/eps` from the equivalence, this
matches the `exp(Omega(1/eps))` alphabet bound that CMM forces on UGC itself, up
to the logarithm. It is therefore the right quantitative shape, not an
artefact.

**Falsifier of the bound's sharpness.** A reduction attaining ratio `C` with
`log k = o(C^2)` would contradict CMM unless `NP <= RP`. A rounding algorithm
reaching `1 - C_0 sqrt(eta)` with `C_0` independent of `k` would refute UGC.

DERIVATION sqrt-scale-ug-alphabet-cost-proof
