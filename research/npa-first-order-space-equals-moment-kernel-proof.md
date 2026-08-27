---
rg: 2
id: npa-first-order-space-equals-moment-kernel-proof
kind: route
title: Cancel the pin against the lambda-line using the face vectors and the universal witness
target: npa-first-order-space-equals-moment-kernel
requires:
  - pakhunov-critical-face-structural-laws
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

`V_k` is a linear space by the pin-homogeneity clause, so counting dimensions is
legitimate.

The kernel law gives `ker Gamma_k(y_0(delta*)) = span N_k`, hence
`Gamma_k(y_0(delta*)) N_k = 0` and a fortiori `Phi_k(y_0(delta*)) = 0`, so
`y_0(delta*)` lies in `ker Phi_k`.  Its identity coordinate is `1`.  Therefore
the linear functional `y |-> y_[identity]` restricted to `ker Phi_k` is not the
zero functional, and its kernel there has codimension exactly `1`:

```text
dim ( ker Phi_k  and  y_[identity] = 0 ) = dim ker Phi_k - 1.
```

The map `(y, lambda) |-> lambda` is onto `R` on `V_k`, because the universal
witness `y*` has `Phi_k(y*) = u_k u_k^T` and identity coordinate `0`, so
`(y*, 1)` lies in `V_k`.  Its fibre over `lambda = 0` is exactly the set
displayed above.  Hence

```text
dim V_k = ( dim ker Phi_k - 1 ) + 1 = dim ker Phi_k.
```

Both inputs are clauses of the imported structural laws; nothing here needs the
germ step or the freeness of unseen coordinates.
