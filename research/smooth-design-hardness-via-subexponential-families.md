---
rg: 2
id: smooth-design-hardness-via-subexponential-families
kind: route
title: Dead -- supply smooth-design richness with a pairing family of subexponential size
target: smooth-design-rich-2to1-hardness
requires: []
---

**Dead.** The attack: meet the smooth-design hypothesis with a small structured
family, e.g. affine, symplectic or bounded-degree polynomial involutions of the
label space, or a `t`-transitive group of moderate size. These are exactly the
families an algebraic outer PCP can produce.

It is killed by `pullback-smoothness-needs-exponentially-many-pairings`. The
density comparison needs at least `(1 - 2^(-Omega(K))) m^n / C(K,m)` pairings,
whatever the family's structure. For separated families the test itself fails
as well (`separated-small-pairing-families-defeat-the-noise-test`).

What survives: families of size at least about `m^n` that still carry algebraic
or combinatorial structure. Low-degree designs composed with random smooth
families are one example.
