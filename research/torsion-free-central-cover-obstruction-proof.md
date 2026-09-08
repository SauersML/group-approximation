---
rg: 2
id: torsion-free-central-cover-obstruction-proof
kind: route
title: Average the central cocycle over the finite subgroup and split it inside the rationalization
target: torsion-free-central-cover-forces-abelian-finite-subgroups
requires: []
artifacts:
  - research/artifacts/torsion-free-transfer-covers-and-obstructions-2026-09-08.md
---

## Proof

Let `P <= G` be finite and replace `E` by `pi^(-1)(P)`, which is again
torsion-free and central over `P`.  The kernel `A` is central, hence abelian,
and torsion-free as a subgroup of `E`, so it embeds in the rational vector
space `V = A tensor_Z Q`.

Choose a set-theoretic section `s : P -> E` with `s(1) = 1` and write the
multiplication defect additively,

```text
s(p)s(q) = c(p,q) s(pq),        c(p,q) in A.
```

Associativity, together with centrality of `A`, gives the cocycle identity

```text
c(p,q) + c(pq,r) = c(q,r) + c(p,qr).
```

Average it over `r in P` and set `b(p) = (1/|P|) sum_r c(p,r) in V`.  The
term `c(p,q)` is constant in `r`; `c(pq,r)` averages to `b(pq)`; `c(q,r)`
averages to `b(q)`; and `c(p,qr)` averages to `b(p)`, since `r -> qr`
permutes `P`.  Hence

```text
c(p,q) = b(p) + b(q) - b(pq).                                           (CC2)
```

Every element of `pi^(-1)(P)` is uniquely `a s(p)` with `a in A`, `p in P`,
and by `(CC2)` the map

```text
a s(p)  ->  (a + b(p), p)   in   V x P
```

is a homomorphism: the product `a s(p) . a' s(q) = (a + a' + c(p,q)) s(pq)`
goes to `(a + a' + b(p) + b(q), pq)`, which is the product of the images.  It
is injective, because `s(1) = 1` forces `c(1,r) = 0` and hence `b(1) = 0`.

The commutator subgroup of `V x P` lies in `{0} x P`, which is finite.  So
the commutator subgroup of `pi^(-1)(P)` embeds in a finite group while being
torsion-free, hence is trivial.  Therefore `pi^(-1)(P)` is abelian, and so is
its quotient `P`.

For the consequence: `G_0 x S_3` contains `G_0`, and subgroups of MF groups
are MF (`mf-positive-controls`), so it is not MF; it contains the nonabelian
finite subgroup `S_3`, so by the theorem it admits no torsion-free central
cover.
