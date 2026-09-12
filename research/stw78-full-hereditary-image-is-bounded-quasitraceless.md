---
rg: 2
id: stw78-full-hereditary-image-is-bounded-quasitraceless
kind: claim
title: Every nonzero LXXVIII image cut has a full bounded-quasitraceless hereditary algebra
distinct_from:
  stw78-layer-quasitraces-need-not-vanish: that theorem shows that a proper nonunital ideal can retain an unbounded lower semicontinuous trace; this theorem concerns full hereditary algebras and excludes every nonzero bounded quasitrace on them.
  stw99-lxxviii-oinfinity-map-has-infinite-image: that theorem derives proper infiniteness of every positive image from O-infinity-stability; this theorem is unconditional before stability and derives only bounded-quasitrace nullity of the hereditary image algebra.
  stw78-simple-comparison-targets-force-oinfinity-stability: that theorem adds simple comparison to turn quasitracelessness into strong pure infiniteness; this theorem uses no comparison and makes no proper-infiniteness conclusion.
artifacts:
  - research/artifacts/stw78-domain-and-full-hereditary-reduction-audit-2026-08-30.md
---

Let `A` be nonzero, unital, and simple, let `B` be unital with no normalized
`2`-quasitrace, and let `phi:A->B` be unital.  For every nonzero
`a in A_+`, put

```text
c=phi(a),                 H_c=closure(cBc).
```

Then `c` is full in `B`, and `H_c` has no nonzero bounded `2`-quasitrace.

More generally, for every full positive `c` in a unital C-star algebra `B`,

```text
B has a normalized 2-quasitrace
  iff closure(cBc) has a nonzero bounded 2-quasitrace.
```

Thus every prospective LXXVIII counterexample already has hereditary
quasitrace nullity at every nonzero positive image cut.  This does not imply
that those hereditary algebras are purely infinite: unbounded lower
semicontinuous quasitraces and comparison perforation remain possible.

