---
rg: 2
id: sl3-double-tensor-leak-is-quasiregular
kind: claim
title: The diagonal tensor witness of a regular SL3 double enemy is exactly quasi-regular, and tensor amplification gives no rigidity gain
artifacts:
  - research/artifacts/sl3-double-tensor-quasiregular-firewall-2026-08-21.md
distinct_from:
  sl3-double-one-near-vertex-forces-joint-near-exactness: that removes an enemy after one vertex approaches an exact representation; this treats the simultaneous two-vertex-outlier sector without any exact anchor.
  sl3-regular-double-collapse-forces-nonsofic-vertex-action: that constructs a conditional group-level countermodel from a sofic action; this identifies the exact pointed representation already carried by every hypothetical regular-double microstate.
  no-exact-quasi-regular-leak: that is the open finite-dimensional exclusion of this profile; this proves the tensor construction lands precisely at that named hole and that property T plus tensor amplification cannot cross it.
---

Let `pi_(n,0),pi_(n,1)` be the two vertex restrictions of canonical-trace
microstates of

```text
D=A *_C A,   A=SL_3(Z[1/2]),   C=SL_3(Z).
```

On `C^(d_n) tensor conjugate(C^(d_n))`, put

```text
rho_n(a)=pi_(n,0)(a) tensor conjugate(pi_(n,1)(a))
```

and let `Omega_n` be the normalized maximally entangled vector.  Then
`rho_n` has vanishing presentation defect and

```text
<rho_n(a)Omega_n,Omega_n>
 = tr(pi_(n,0)(a)pi_(n,1)(a)^*)
 -> 1_C(a).                                                (TQR1)
```

Thus the cyclic pointed Hilbert-ultraproduct representation is exactly
`(lambda_(A/C),delta_C)`.  In particular property (T) of `C` or of `A`
cannot turn `Omega` into an `A`-invariant vector: the exact quasi-regular
representation is the obstruction, not an approximation error.

For `k` tensor copies, relator and `C`-invariance errors grow at best by
the usual tensor scales

```text
def(rho_n^(tensor k)) <= k def(rho_n),
||rho_n(c)^(tensor k)Omega_n^(tensor k)-Omega_n^(tensor k)||_2^2
 =2-2 Re(<rho_n(c)Omega_n,Omega_n>^k),                     (TQR2)
```

while the limiting pointed coefficient remains
`1_C(a)^k=1_C(a)`.  Fixed tensor or exterior powers therefore reproduce
the same quasi-regular wall; growing powers must satisfy a shrinking-error
condition and still do not create an `A`-almost-invariant cyclic vector.

Consequently this lane closes the fold only by resolving the already named
hole `no-exact-quasi-regular-leak` for the SL3 pair (or a stronger relative
embeddability/action-soficity obstruction).  It does not reduce to ordinary
property (T), and it does not secretly require full HS stability of `A`.

