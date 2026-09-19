---
rg: 2
id: twisted-regular-predicate-trace-proof
kind: route
title: Expand the twisted Fourier coefficient norm and pass to a central-character corner
target: twisted-regular-predicate-projections-have-positive-trace
requires:
  - thom-central-corner-criterion
---

The canonical twisted basis is orthonormal in `L^2(L_omega(Gamma),tau)`.
Since `p=p^*p`,

```text
tau(p)=tau(p^*p)=||p||_2^2=sum_g |c_g|^2.
```

For a finite central extension, Fourier compression by `q_chi` identifies the
normalized corner basis with the twisted basis.  Applying the first
calculation in that corner proves every clause.
