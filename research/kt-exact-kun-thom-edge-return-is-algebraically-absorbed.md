---
rg: 2
id: kt-exact-kun-thom-edge-return-is-algebraically-absorbed
kind: claim
title: Every exact Kun--Thom vertex representation absorbs the compressor return into its edge algebra
distinct_from:
  kt-double-shortest-fold-repair-is-a-bare-wall: that proves two exact vertex representations agreeing on Gamma have the same compressor return; this applies that theorem against every commutant gauge and derives edge-algebra membership for one arbitrary representation.
  kt-finite-image-relative-edge-models-are-impossible: that uses nonsoficity of the coset action to exclude blockwise weighted quotient models which approximate all exterior expectations; this gives expectation norm one for one fixed exterior return in every exact finite-dimensional representation, including infinite-image and cross-block-coupled ones.
  kt-edge-expectation-is-a-moving-coset-gram-supremum: that gives the exact variational formula and shows why canonical characters alone do not control it; this evaluates the formula at one Kun--Thom return using finite-dimensional folding.
---

**ESTABLISHED.**  Fix a strict Kun--Thom compressor

```text
t Gamma t^(-1)<Gamma,
```

choose `gamma in Gamma minus t Gamma t^(-1)`, and put

```text
h=t^(-1) gamma t notin Gamma.                           (KEA1)
```

For every finite-dimensional exact unitary representation
`pi:G->U(d)`,

```text
pi(h) in C*(pi(Gamma)).                                 (KEA2)
```

Consequently, if `B=C*(pi(Gamma))`, then

```text
E_B(pi(h))=pi(h),              ||E_B(pi(h))||_2=1.      (KEA3)
```

The conclusion permits arbitrary direct sums, repeated or inequivalent
Gamma types, cross-block coupling, and finite-dimensional representations
with infinite image.  Thus no construction whose vertex coordinates are
honest representations can approximate the canonical inclusion expectation
at this single exterior element.  In particular, deleting constant vectors
from profinite regular blocks does not open a reduced-amalgam route.

Any positive proof of `kt-double-reduced-cstar-is-mf` through relative
matrix models must use genuinely approximate vertex maps whose failure of
exactification occupies the edge-return geometry itself.  Randomizing the
commutant of an exact vertex representation cannot help, because `(KEA2)` is
fixed by that entire commutant.

DERIVATION
kt-exact-edge-return-absorption-proof
