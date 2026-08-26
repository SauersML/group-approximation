---
rg: 2
id: shulman-presentation-double-witnesses-have-adjoint-normal-form
kind: claim
title: Shulman presentation-double witnesses can be chosen in one adjoint Julia normal form
distinct_from:
  shulman-double-forces-unstable-kernel-restriction: that extracts arbitrary exact vertex-representation pairs from weak MF; this proves that a witnessing choice can be made globally conjugate and identifies its left-right representation with one adjoint representation.
  leavitt-positive-rank-intertwiner-retention: that asks for a trace-visible almost-quotient sector; this identifies the precise positive spectral sector where such a witness would have to live but supplies no normalized-rank bound.
  weak-mf-embedding-not-reusable: that is the general norm-versus-tracial firewall; this is the free-vertex specialization and records the exact finite-coordinate normal form which survives that firewall.
artifacts:
  - notes/SHULMAN_PRESENTATION_DOUBLE_JULIA_AUDIT_2026-08-26.md
---

**ESTABLISHED.** Let `Q=F/K` be an infinite finitely generated simple
nonsofic quotient of a finitely generated free group, and fix `f_0 in F\K`.
The unstable pairs in
`shulman-double-forces-unstable-kernel-restriction` may be chosen in the
form

```text
sigma_n:F->U(d_n),                 exact,
V_n in U(d_n),
v_n=sigma_n,
u_n=V_n^* sigma_n V_n,                            (SJA1)
```

so that

```text
||[sigma_n(k),V_n]||_op -> 0       for every fixed k in K,
||[sigma_n(f_0),V_n]||_op >= c>0   along a tail.   (SJA2)
```

The dimensions come from a fixed fourfold Julia stabilization of one inner
matrix coordinate.  Under the Hilbert--Schmidt unitary `T |-> V_n T`, the
left-right representation

```text
Pi_n(f)T=u_n(f)T v_n(f)^*
```

is exactly the adjoint representation

```text
Ad(sigma_n)(f)S=sigma_n(f)S sigma_n(f)^*.           (SJA3)
```

Moreover restriction rigidity gives the exact equality

```text
Fix(Ad(sigma_n)(K))=sigma_n(K)'
                   =sigma_n(F)'
                   =Fix(Ad(sigma_n)(F)).             (SJA4)
```

Thus the zero-energy `K`-intertwiner sector is already `F`-fixed and cannot
retain `f_0`.  Any solution of
`leavitt-positive-rank-intertwiner-retention` obtained from these witnesses
must use positive eigenvalue bands of the finite kernel-intertwiner
Laplacians whose eigenvalues collapse to zero, while those bands become
almost reducing for `Ad(sigma_n)(F)` and still see `f_0`.

Shulman's proof gives no multiplicity or normalized-rank estimate for those
bands.  Its quasicentral cutoff is selected only in operator norm, and an
arbitrarily large common exact summand can be inserted in the escaping
finite-coordinate tail without changing the strong quotient, the edge
error, or operator-norm separation.  Therefore `(SJA1)--(SJA4)` sharpen the
open retention problem but neither prove nor refute it.

DERIVATION
shulman-presentation-double-adjoint-normal-form-proof
