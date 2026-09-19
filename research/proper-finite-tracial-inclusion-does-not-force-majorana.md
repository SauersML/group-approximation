---
rg: 2
id: proper-finite-tracial-inclusion-does-not-force-majorana
kind: claim
title: Proper finite tracial inclusions need not contain a Majorana pair
distinct_from:
  relative-wall-commutant-growth: that theorem identifies strict compressor growth with a bare noncommuting wall; this counterexample shows that strictness alone does not upgrade the wall to exact anticommutation.
  compressed-commutant-majorana: that asks for a Majorana inside a relative commutant arising from the specific Kun--Thom actor; this only refutes the abstract inference from proper inclusion, and does not decide whether the actor supplies additional structure.
  bare-relative-wall-exists: that asks for one strict relative-commutant inclusion in a Connes-embeddable representation of the Kun--Thom group; this separates the Clifford strengthening after such an inclusion has been found.
---

There is a proper unital inclusion of finite tracial von Neumann algebras

```text
N < P
```

for which no two self-adjoint involutions in `P` anticommute.  In particular,
properness of a relative-commutant inclusion cannot, by itself, supply the
Majorana condition in `compressed-commutant-majorana`.

Take

```text
N = C 1 < P = C direct_sum C
```

with the average trace.  The algebra `P` is commutative.  If self-adjoint
unitaries `v,w in P` anticommuted, then commutativity would give

```text
vw = wv = -wv,
```

hence `2vw=0`.  But `vw` is a unitary, a contradiction.  Thus strict growth
does imply a bare element outside the smaller algebra, but exact
anticommutation is genuinely extra data.

This does not refute the Kun--Thom Majorana claim: a compressor inclusion has
the additional constraint that its two endpoints are inner conjugate inside
one ambient finite algebra.  It does close the proposed *formal* shortcut
from `N != N_t` to a Clifford wall, which used none of that extra geometry.
