---
rg: 2
id: no-finite-arithmetic-hecke-corner-can-have-shell-atom-trace
kind: claim
title: No finite arithmetic Hecke corner can have the forty-two-shell atom trace
distinct_from:
  sl3-one-over-forty-two-packet-is-external-or-folded: That treats finite subgroup atoms and exact finite quotient packets as two proposed global shell sources; this extracts the immediate uniform consequence for every finite-Hecke A2 wordization attempt.
  native-c2-hecke-corner-cannot-wordize-the-a2-average: That computes support and covariance for one favorable involution packet; this closes all finite `K<D` at once using trace before those finer tests are reached.
  finite-subgroup-hecke-literals-cannot-block-escape: That classifies projections of the form `qgq`; this rules out the source corner `q` itself at the required canonical trace, whether or not `qgq` is a projection.
---

Let

```text
D=SL_3(Z) cap hSL_3(Z)h^(-1),
h=diag(2,1,1/2),                                      (FHC1)
```

let `K<D` be finite, and let `q` be any nonzero projection in `C[K]`.
This includes every character idempotent and every sum or matrix
subprojection of finite `K`-types.  The canonical group trace restricts to
the normalized regular trace of `K`, so

```text
tau(q)=rank(lambda_K(q))/|K|.                          (FHC2)
```

Every finite subgroup of `SL_3(Z[1/2])<SL_3(Q)` is rationally conjugate
into `SL_3(Z)` and has order at most `24`, by the finite-subgroup
classification already recorded in
`sl3-one-over-forty-two-packet-is-external-or-folded`.  If

```text
tau(q)=1/42,                                           (FHC3)
```

then `(FHC2)` would give

```text
42 rank(lambda_K(q))=|K|,                              (FHC4)
```

impossible because the left side is at least `42` and the right side is at
most `24`.

Consequently no finite `K<D` and no character idempotent `q in C[K]` can
simultaneously satisfy the three desired properties

```text
tau(q)=1/42,
q retains the D-section covariance,
qgq has the two A2 path supports with relative holonomy x_23(2).           (FHC5)
```

The first row alone is impossible.  No support enumeration, character
choice, covariance estimate, or amplification **inside one finite
arithmetic subgroup** can change this conclusion.

The scope is exact.  It does not rule out:

1. multiplying a finite lamp corner by a projection from an infinite or
   diffuse commuting algebra;
2. an infinite-support Borel/Hecke projection in a von Neumann completion;
3. a matrix-coordinate projection whose defining depth tends to infinity;
4. a noncentral corner in a larger arithmetic-lamp group rather than in
   `C[K]` for `K<D`.

Each escape has left the finite-Hecke class.  In particular, replacing
`1/42` by an approximate trace does not help a fixed `K`: the finite set of
possible ranks in `(FHC2)` has a positive distance from `1/42`.

