---
rg: 2
id: infinite-stabilizer-trivial-homoclinic-proof
kind: route
title: Keep one nontrivial coordinate visible along its infinite stabilizer
target: infinite-stabilizer-coset-bernoulli-has-trivial-homoclinic-group
requires: []
---

Take `x in K` with `x(y)!=1` at some coset `y in Lambda/P`.  The stabilizer
`Lambda_y` is a conjugate of `P`, hence infinite.  Choose distinct
`g_n in Lambda_y`; then `g_n -> infinity` in the discrete group.  Under the
coordinate-shift convention,

```text
(g_n.x)(y)=x(g_n^(-1)y)=x(y)!=1
```

for every `n`.  Evaluation at `y` is continuous in the product topology, so
`g_n.x` does not converge to the identity configuration.  Therefore `x` is
not homoclinic.  Since this holds for every nonidentity `x`, `(ICH1)` follows.

The point is specific to coset shifts.  For the regular shift indexed by
`Lambda`, stabilizers are trivial and finite-support configurations are
homoclinic and dense.  For an infinite-stabilizer coset shift, even a
one-coordinate configuration is pinned along infinitely many group elements.
