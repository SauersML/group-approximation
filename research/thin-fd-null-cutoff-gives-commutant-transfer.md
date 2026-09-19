---
rg: 2
id: thin-fd-null-cutoff-gives-commutant-transfer
kind: route
title: Apply the universal cutoff to turn selected upper semicontinuity into thin commutant transfer
target: thin-sln-robust-relative-commutant-transfer
requires:
  - thin-leak-has-universal-fd-null-laplacian-witness
  - thin-selected-fd-null-cutoff-cannot-survive-matrices
---

In the tracial matrix ultraproduct, a unitary centralizing `C` satisfies by
`(ULW4)`

```text
||alpha(y_N)v||_2=||[v,pi(r)]-1||_2                    (1)
```

for every `N`.  The left side tends to zero by `(SFC1)`, so the marked
commutator vanishes.  This proves the qualitative ultraproduct transfer.
If the dimension-free finite-stage modulus failed, a sequence of failures
would give exactly such an ultraproduct counterexample; compactness therefore
gives `(TRC1)`.
