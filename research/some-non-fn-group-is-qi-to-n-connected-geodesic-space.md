---
rg: 2
id: some-non-fn-group-is-qi-to-n-connected-geodesic-space
kind: claim
title: Some group not of type F_n is quasi-isometric to an (n-1)-connected proper geodesic space
distinct_from:
  every-fg-group-is-qi-to-a-contractible-proper-space: that claim uses a non-geodesic metric and holds for every group; this claim asks for a geodesic metric, where a length metric forbids the spanning-tree shortcut
---

For some n ≥ 3 there is a finitely generated group G that is not of type F_n
but is quasi-isometric to a proper geodesic metric space X that is
(n − 1)-connected.

This is the negative answer to Zaremsky Problem 1.3 under the geodesic
reading (`zaremsky-1-03-qi-to-connected-space-implies-type-fn`). The case
n = 2 cannot occur: a finitely generated group quasi-isometric to a simply
connected proper geodesic space is finitely presented (lane z1-03-qi-fn,
write-up landing).

## Attempts

- Kill `pi_2` of a presentation complex far away (lane z1-03-qi-fn,
  2026-09-13). Let G be finitely presented but not of type F_3 (e.g. the
  Stallings–Bieri group SB_3), and let Y be the universal cover of a finite
  presentation complex. By Hurewicz, killing H_2(Y) by 3-cells gives a
  2-connected space. It dies twice:
  - The cells must be locally finite for properness. A generating set of
    H_2(Y) in which each 2-cell lies in only finitely many generators would
    be needed, and the naive elimination (H_2 modulo cycles avoiding B_k
    embeds in C_2(B_k), so it is finitely generated at each stage) need not
    terminate.
  - Worse, the filling 3-cells must be quasi-isometrically invisible: every
    point within bounded distance of Y, and no shortcut between boundary
    points. A cone of height about the diameter of the sphere violates the
    first condition, and a thin ball exists only for spheres that are
    coarsely folded discs.

  Any counterexample X therefore has to change the coarse fillings of small
  loops (non-uniform simple connectivity) rather than only add thin 3-cells.
- Needed input for any counterexample: X has small loops, arbitrarily far
  out, whose fillings in X have unbounded diameter. This is forced by
  `fg-group-qi-to-n-connected-geodesic-space-is-type-fn`'s uniform version.
