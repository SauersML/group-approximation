---
rg: 2
id: stw99-problem-lxvi-car-embedding-with-finite-projection
kind: claim
title: A simple infinite C*-algebra contains a unital CAR algebra whose image has a nonzero finite projection (STW Problem LXVI)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw99-lxvi-coherent-car-no-go-audit-2026-08-30.md
---

**Problem LXVI of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras:
99 problems*, arXiv:2506.10902v2.**  Does there exist a simple unital infinite
C\*-algebra `B` and a unital embedding

```text
phi : M_(2^infinity) -> B
```

whose image contains a nonzero finite projection?

The problem is open.  Rordam's mixed finite/infinite simple algebra gives the
finite-stage analogue with `M_2` in place of the CAR algebra.  The exact
corner reduction `stw99-lxvi-iff-finite-car-corner-with-infinite-double`
shows that the remaining issue is not coherence of infinitely many matrix
units by itself: it is whether a unital CAR algebra can live inside a simple
finite algebra whose `2 x 2` amplification is infinite.

The prescribed amplification index is now known to be inessential.
`stw99-lxvi-finite-car-seed-amplification-index-is-irrelevant` proves that it
is enough to construct a simple unital finite but non-stably-finite algebra
containing a unital CAR algebra.  Passing to the matrix algebra immediately
below its first infinite amplification produces the required `2 x 2` seed.

## Attempts

The active attack is `stw99-lxvi-via-finite-car-corner`.  It reduces the
problem to one construction rather than deferring it: build the CAR algebra
inside a finite simple corner while its double is already infinite.
The parallel route `stw99-lxvi-via-nonstable-finite-car-seed` removes the
need to prescribe which finite amplification first becomes infinite.

There is a new broad obstruction to installing the coherent CAR tower.
`stw99-lxvi-finite-index-car-envelopes-are-stably-finite` proves that a
finite Watatani-index expected extension of any stably finite core is stably
finite, by embedding the ambient algebra into a fixed matrix corner over the
core.  Hence an LXVI witness cannot admit a finite-index conditional
expectation onto its CAR copy.  This rules out finite-group crossed products
of CAR, finite towers of finite-index expected extensions, and injective
limits built from such stages.  A successful CAR inclusion must have
genuinely infinite module index; no trace, `K_0`, or centrality hypothesis is
used in this obstruction.

Infinite index does not rescue the standard free constructions.
`stw99-lxvi-tracial-free-constructions-are-stably-finite` proves that every
reduced crossed product of CAR by an arbitrary discrete group is stably
finite: the unique CAR trace is invariant and its composition with the
faithful coefficient expectation is a faithful trace.  The same vacuum-trace
argument covers reduced amalgamated free products over CAR whenever the leg
expectations are faithful and trace preserving, as well as ordinary reduced
free products of CAR with faithfully tracial factors.  If the corresponding
full construction is simple, its quotient onto the reduced construction is
injective and it is stably finite too.  Thus crossed-product and
trace-preserving free-product assembly are unavailable even at infinite
Watatani index; passing to corners or injective limits of such corners cannot
repair the obstruction.

HNN extensions face a sharper spectral dichotomy.
`stw99-lxvi-car-hnn-trace-balance-dichotomy` proves that, inside any finite
unital ambient algebra containing CAR, two unitarily conjugate positive CAR
elements must have the same CAR trace.  A trace mismatch appears at a
spectral cutdown; strict comparison in CAR then absorbs a nonzero CAR
projection into that cutdown, and fullness makes the ambient unit properly
infinite.  Hence an HNN covariance between arbitrary edge embeddings must
preserve the induced CAR trace.  This closes even the projectionless escape:
explicit embeddings of `C([0,1])` given by `f |-> f(h)` and `f |-> f(h^2)`
agree on every projection but have traces `1/2` and `1/3` on the coordinate
function, and every covariance unitary makes the ambient unit properly
infinite.  For a finite-dimensional edge, trace balance supplies a faithful
trace on the reduced HNN algebra (and on a simple full HNN algebra), making
it stably finite.  Thus the non-trace-preserving HNN escape is closed at the
level of all positive elements, not merely projections.

A second broad no-go concerns ambient regularity rather than the CAR
inclusion.  `stw99-lxvi-z-stability-forbids-mixed-projections` proves that a
simple unital Z-stable algebra is either stably finite or has every nonzero
projection properly infinite.  Thus an LXVI witness cannot be Z-stable,
regardless of how noncentral or infinite-index its CAR copy is.  In
particular, every separable witness has infinite nuclear dimension: finite
nuclear dimension would imply Z-stability in the non-elementary simple case,
while the elementary case cannot contain an infinite projection.

There is also a direct consequence for another STW problem:
`stw99-lxvi-witness-refutes-lxxviii` proves that every LXVI witness yields a
counterexample to Problem LXXVIII.  Thus a construction here would settle
both problems, with opposite signs.
