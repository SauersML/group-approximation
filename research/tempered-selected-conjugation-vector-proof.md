---
rg: 2
id: tempered-selected-conjugation-vector-proof
kind: route
title: Apply the reduced C-Laplacian to the selected conjugation orbit
target: tempered-selected-conjugation-vector-obeys-rcc
requires: []
---

Fix a finite symmetric generating set `S_C` and put

```text
Delta_C=sum_(s in S_C)(1-s)^*(1-s) in C[C].             (1)
```

Nonamenability of `C` gives a positive bottom spectral gap in the left
regular representation:

```text
lambda_C(Delta_C) >= kappa_C I                          (2)
```

for some `kappa_C>0`.  On restriction to `C`, the left regular
representation of `A` is a direct sum of copies of `lambda_C`, one for
each left `C`-orbit in `A`.  Weak containment is preserved by restriction.
Therefore `(TSV2)` implies that `alpha|_(K_U)` factors through
`C^*_r(C)` on restriction to `C`, and positivity of `(2)` gives

```text
kappa_C ||eta||_2^2
 <= <alpha(Delta_C)eta,eta>
 = sum_(s in S_C)||alpha(s)eta-eta||_2^2.               (3)
```

The projection `P_A` commutes with `alpha(A)`, and `P_AU` is fixed by
all of `A`.  Hence

```text
alpha(s)eta-eta=alpha(s)U-U.                            (4)
```

For a unitary `U`, tracial invariance gives

```text
||alpha(s)U-U||_2=||[U,pi(s)]-1||_2.                   (5)
```

Equations `(3)--(5)` prove `(TSV3)`.  Finally, for every `a in A`,

```text
||[U,pi(a)]-1||_2
 =||alpha(a)U-U||_2
 =||alpha(a)eta-eta||_2
 <=2||eta||_2,                                         (6)
```

which together with `(TSV3)` proves `(TSV4)`.

If a `C`-central unitary is not `A`-central, then `eta` is a nonzero
`C`-fixed vector in `K_U`.  Were `K_U` weakly contained in `lambda_A`,
restriction to `C` would put the trivial representation of `C` weakly
inside `lambda_C`, contradicting nonamenability.  This proves the final
localization statement as well.
