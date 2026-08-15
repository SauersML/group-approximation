---
rg: 2
id: spectral-component-motion-bound-proof
kind: route
title: Fixed clopen sets pin characters to quasi-components
target: spectral-component-motion-bound
requires: [corona-projection-collapse]
---

## Why sufficient

Let `U <= sigma(v)` be clopen and `p_U = 1_U(v)` its spectral projection.
As in `zero-dimensional-spectral-collapse-proof`, `p_U` satisfies the two
hypotheses of `corona-projection-collapse`, so

```text
pi(gamma) p_U pi(gamma)^* = p_U        for every gamma in L.
```

Put `w = pi(gamma) v pi(gamma)^*`.  Functional calculus commutes with
conjugation, so `1_U(w) = 1_U(v)` for every clopen `U`.

`v` and `w` commute (hypothesis 2 at the pair `(1, gamma)`), so
`A = C*(v, w, 1)` is commutative.  For a character `chi` of `A` put
`z = chi(v)`, `z' = chi(w)`; both lie in `sigma(v)` (the spectrum of `w`
equals that of `v`).  For every clopen `U`, applying `chi` to
`1_U(w) = 1_U(v)` shows `z in U` iff `z' in U`: the two points lie in
exactly the same clopen subsets of `sigma(v)`, hence in the same
quasi-component.  In a compact Hausdorff space quasi-components coincide
with connected components, so `|z - z'| <= diam(C)` for the common
component `C`.  Taking the supremum over characters of `A` gives the
operator-norm bound for `w - v`.
