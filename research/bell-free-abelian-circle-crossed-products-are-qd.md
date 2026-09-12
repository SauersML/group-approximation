---
rg: 2
id: bell-free-abelian-circle-crossed-products-are-qd
kind: claim
title: Free countably infinite abelian circle-action crossed products are quasidiagonal
distinct_from:
  stw99-problem-xi-zd-crossed-stably-finite-qd: that asks for quasidiagonality and AF embeddability of every stably finite Z^d crossed product; this is the quasidiagonality conclusion only, for free actions on the circle, and makes no AF-embedding assertion.
  stw11-folner-capacity-faithful-trace-criterion: that reaches actions carrying a faithful invariant probability measure; a non-minimal free circle action has its invariant probability supported on its proper minimal set, and this theorem instead crosses the resulting non-simple extension.
  stw11-lattice-coupled-cyclic-products-are-af-embeddable: that treats actions assembled from powers of finitely many independent cyclic systems and obtains an AF embedding; this permits an arbitrary free abelian action on one circle but proves only quasidiagonality.
artifacts:
  - research/artifacts/stw11-bell-circle-actions-primary-source-2026-08-30.md
---

Let `G` be a countably infinite discrete abelian group and let
`G -> Homeo(T)` be a free action on the circle.  Then

```text
C(T) rtimes G
```

is quasidiagonal.

Because `G` is amenable, the full and reduced crossed products agree.  No
minimality assumption is present.  In particular, for every `d >= 2` this
gives the quasidiagonality half of STW Problem XI for free
`Z^d`-actions on the circle, including the non-minimal case where the unique
invariant probability measure need not have full support.

The result does **not** assert AF embeddability.  The primary source explicitly
records that stronger conclusion as unverified in the non-minimal case.
