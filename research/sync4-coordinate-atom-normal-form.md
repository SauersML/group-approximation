---
rg: 2
id: sync4-coordinate-atom-normal-form
kind: claim
title: SYNC4 hardness is equality of degree-two atom reflections on pairs of commuting involutions
artifacts:
  - research/artifacts/culf-mastel-sync-normal-form-2026-08-23.md
distinct_from:
  fixed-sync-k-language-is-re-hard: that gives the fixed hard language for every k; this chooses k=4 and rewrites every PVM and losing edge in binary Fourier coordinates.
  all-bcs-contexts-share-one-hyperoctahedral-signed-type: that balances arbitrary BCS contexts in a large common signed type; this source already has four outcomes and one atom per edge.
  low-dimensional-hyperoctahedral-packet-groupifies-any-predicate: that gives a general predicate packet; this isolates only the exact atom-reflection equality energy.
---

**ESTABLISHED.**  Identify `Z_4` with `F_2^2` by any fixed computable
bijection.  A four-outcome PVM `(E_a)_(a in F_2^2)` is equivalent to two
commuting involutions

```text
A=sum_a (-1)^(a_1) E_a,
B=sum_a (-1)^(a_2) E_a,                                (S4N1)
```

with inverse Fourier formula

```text
E_(u,v)=1/4 (1+(-1)^u A)(1+(-1)^v B).                  (S4N2)
```

The atom reflection is

```text
R_(u,v)=1-2E_(u,v)
       =1/2(1-(-1)^u A-(-1)^v B-(-1)^(u+v)AB).         (S4N3)
```

It is a self-adjoint unitary.  Every hard `SYNC_4` edge has exactly the
energy

```text
||E_j(y)-E_0(x)||_2^2
 =1/4 ||R_j(y)-R_0(x)||_2^2
 =1/4 ||R_j(y)R_0(x)-1||_2^2.                          (S4N4)
```

Thus the target no longer contains an arbitrary nonlinear predicate: it is
only equality of one atom reflection at each endpoint.  Formula `(S4N3)` is
an identity in the local commutative algebra, not yet an ordinary group-word
identity.  The exact wordization without an equal-rank assumption is supplied
by `sync4-one-negative-abelian-corner-wordizes-arbitrary-pvm`.
