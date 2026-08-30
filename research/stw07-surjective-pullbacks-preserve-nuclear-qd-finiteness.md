---
rg: 2
id: stw07-surjective-pullbacks-preserve-nuclear-qd-finiteness
kind: claim
title: Surjective pullbacks preserve the nuclear stably finite quasidiagonal class
distinct_from:
  stw07-local-qd-subalgebras-force-quasidiagonality: that theorem approximates the ambient algebra from inside by subalgebras; this theorem embeds a pullback into a finite direct sum of quotient-coordinate pieces.
  stw07-mixed-local-solved-models-are-qd: that claim requires norm-local approximation by solved subalgebras, whereas this claim permits recursive quotient gluings of solved pieces.
  stw99-problem-vii-blackadar-kirchberg: this is a pullback permanence class and does not assert that an arbitrary nuclear stably finite algebra has quasidiagonal coordinates.
artifacts:
  - research/artifacts/stw07-status-and-stable-character-reduction-2026-08-30.md
---

Let `phi:B -> C` and `psi:D -> C` be star homomorphisms of C-star algebras,
with `phi` surjective, and form the pullback

```text
P = B fiber_product_C D
  = {(b,d) in B direct_sum D : phi(b)=psi(d)}.
```

If `B` and `D` are separable, nuclear, stably finite, and quasidiagonal, then
`P` has all four properties.  The same conclusion holds for every finite
iterated pullback tree whose leaves have these properties and for which at
least one map at each gluing node is surjective.

Consequently, the leaves may independently be chosen from either of the
following solved Blackadar--Kirchberg classes:

1. separable nuclear stably finite traceless algebras;
2. separable nuclear UCT algebras carrying a faithful tracial state.

Every finite surjective pullback tree built from such a mixture is a
separable nuclear stably finite quasidiagonal algebra.  Thus Problem VII has
a positive answer on this recursively glued class even when the leaf type
changes from one branch to another.
