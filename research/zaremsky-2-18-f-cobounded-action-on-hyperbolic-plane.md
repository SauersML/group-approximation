---
rg: 2
id: zaremsky-2-18-f-cobounded-action-on-hyperbolic-plane
kind: claim
title: "Zaremsky Problem 2.18 resolved: does Thompson's group F admit a cobounded action by isometries on the hyperbolic plane?"
root: true
distinct_from:
  thompson-f-has-no-cobounded-action-on-hyperbolic-plane: that claim is the negative answer under the literal reading (isometries of the real hyperbolic plane itself); this claim is the list question, which also asks about spaces quasi-isometric to the plane
  thompson-f-has-no-cobounded-action-on-spaces-qi-to-h2: that claim is the negative answer for geodesic spaces quasi-isometric to the plane; this claim is the list question itself, established only through its answer route
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 18, verbatim:
"(Added 6/19/24) Does Thompson's group F admit a cobounded action by isometries on
the hyperbolic plane?"

This claim is the question. It is established only through an answer route:

- **No**: `zaremsky-2-18-by-no` requires both
  `thompson-f-has-no-cobounded-action-on-hyperbolic-plane` (literal reading) and
  `thompson-f-has-no-cobounded-action-on-spaces-qi-to-h2` (source reading).
- **Yes**: a route requiring a claim that exhibits such an action. None is recorded:
  the literal reading is refuted (see below).

Never write a `requires: []` route into this claim.

## Precise reading

- *Cobounded*: some (equivalently every) orbit is coarsely dense.
- *Literal reading*: an isometric action of `F` on the real hyperbolic plane `H^2`.
  This is settled negatively by `thompson-f-has-no-cobounded-action-on-hyperbolic-plane`
  (proof written, unreviewed).
- *Source reading*. The item was added on 6/19/24, one day after arXiv:2406.12982v1
  (S. Balasubramanya, F. Fournier-Facio, M. C. B. Zaremsky, *Hyperbolic actions of
  Thompson's group F and generalizations*, 18 June 2024). Its Question 11.4
  (v1 pp. 55–56; the same in v2 of 14 April 2026), verbatim: "We have seen in
  Propositions 2.15 and 2.16 that quasi-parabolic structures representable by actions
  on trees correspond to discrete characters and confining subgroups (see also Remark
  2.17). It follows that many of the hyperbolic structures constructed in this paper
  are not representable by actions on trees. These include some lamplike (Remark 8.12)
  and all non-lamplike structures (Theorem D). What spaces arise for those? In
  particular, are they all representable by actions on quasi-trees? Are any of them
  representable by actions on (a space quasi-isometric to) the hyperbolic plane ℍ²?"
  So the intended question includes cobounded isometric actions on geodesic spaces
  quasi-isometric to `H^2`, i.e. hyperbolic structures of `F` (Abbott–Balasubramanya–Osin)
  whose Cayley graphs are quasi-isometric to `H^2`. This root requires that reading too.
- Known structure (arXiv:2406.12982, Theorem A): `F_n` has no general type structures,
  and its quasi-parabolic structures form two isomorphic posets attached to the two
  endpoint characters.

## Attempts

- 2026-09-13 (lane z2-18-f-h2-action): literal reading answered NO by linearity (Tits
  alternative) plus simplicity of `[F,F]`; see
  `thompson-f-has-no-cobounded-action-on-hyperbolic-plane-proof`. Unreviewed.
- 2026-09-13: source reading reduced to rigidity of uniform quasi-actions on `H^2`
  (uniformly quasisymmetric circle groups are quasisymmetrically conjugate to Möbius
  groups, V. Markovic, J. Amer. Math. Soc. 19 (2006)); the imported statements are not
  yet verified from sources. See `thompson-f-has-no-cobounded-action-on-spaces-qi-to-h2`.
