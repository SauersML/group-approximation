---
rg: 2
id: stw99-problem-xl-amenable-actions-exact-groups
kind: claim
title: Every exact nonamenable group acts amenably on a unital stably finite classifiable algebra (STW Problem XL)
root: true
distinct_from:
  amenable-action-invariant-trace-forces-amenability: that established theorem says such actions preserve no trace and fix no measure on T(A); it constrains but does not decide this existence question, which asks whether the surviving Poulsen-type targets actually occur.
artifacts:
  - research/artifacts/stw99-presentations-cartan-cluster-2026-08-30.md
---

**Problem XL of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Does
every countable discrete exact non-amenable group act amenably on a
unital stably finite classifiable C\*-algebra?  (Exactness is
necessary: amenable actions on nuclear algebras force exactness.
Kirchberg-algebra analogues exist — Szabo's equivariant `O_∞`-stability
covers amenable actions of non-amenable groups on Kirchberg algebras —
and every exact group acts amenably on some compact space, but those
crossed products are traceless or non-simple/non-classifiable.)

## Attempts

* Hard constraint established this session
  (`amenable-action-invariant-trace-forces-amenability`): the action
  can preserve no trace, and the affine action on `T(A)` can carry no
  invariant measure.  So candidate targets are pinned: `T(A)` must
  admit a measure-fixed-point-free affine action of `G` — the Poulsen
  simplex does (it is universal for such dynamics), and stably finite
  classifiable algebras with Poulsen simplex exist in abundance, so
  the obstruction does not close the problem; it dictates the shape of
  any construction: an amenable `G`-action on a Poulsen-simplex
  classifiable algebra covering a boundary-type action on `∂T(A)`.
  The natural candidate is a classifiable model of a boundary action
  (crossed-product-by-hyperbolic-boundary data made stably finite via
  orbit-breaking in the sense of Deeley--Putnam--Strung), where
  amenability of the original boundary action should persist to the
  broken groupoid; nothing of this kind is in the literature.
