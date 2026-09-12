---
rg: 2
id: finite-ground-energy-via-expansion-and-collision-corners
kind: route
title: Use ground periods and expansion to recover bounded energy sectors
target: finite-ground-pattern-energy-forces-surjectivity
requires:
  - relative-equality-piecewise-injections-are-surjective
artifacts:
  - research/artifacts/finite-ground-energy-and-compiler-obstruction-2026-09-08.md
---

Finite-configuration injectivity implies preinjectivity by localizing
an asymptotic collision to a finite input pair. If G is amenable, the
Myhill theorem gives full-shift surjectivity.

Otherwise the kernel H of the G-action on the finite zero-energy set
has finite index and is nonamenable. Choose finitely many directions
S in H with a uniform finite-set expansion constant. Every ground
configuration agrees at 1 and s for s in S. Compactness therefore
detects each disagreement x(g)!=x(gs) by a charged center in one
fixed finite neighborhood. The expansion boundary of supp(x) consists
of such disagreements, giving |supp(x)|<=C E(x).

For each fixed energy bound q, this bounds the size of every support
component. A nonempty component for the P^(-1)P adjacency must contain
a charged pattern, since the support estimate excludes nonzero
finite zero-energy configurations. Thus all its sites lie within a
finite, q-dependent neighborhood of a charged center.

Use this neighborhood to decorate the energy tokens. The attached
proof checks that the integer packet reduction, level induction,
finite relative-equality domains, and equivariant matching of free
stabilizer token sets from the singleton-ground proof still apply.
The required collision claim fills each level. Its radius may depend
on q; no uniform-in-energy detection radius is needed.

The amenable branch imports the Myhill implication; the artifact
cites its primary source and proves the localization needed to meet
its preinjectivity hypothesis. The nonamenable branch uses the
finite-set expansion characterization and finite-index permanence
of amenability, followed by the explicit collision argument.
