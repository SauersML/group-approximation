---
rg: 2
id: rational-polytope-exchange-groups-are-lef
kind: claim
title: Every finitely generated group of rational polytope exchanges of a torus is LEF
distinct_from:
  interval-exchange-groups-are-lef: that is the one-dimensional case, interval exchanges of the circle; this covers tori of every dimension, with pieces cut out by affine conditions with integer normal vectors
  labbe-shift-derived-full-group-is-lef: that asks LEF for the full group of Labbé's shift, whose partition has the irrational edge direction (1, -φ), where rational specialisation produces slivers; this proves LEF exactly when every facet normal is an integer vector
  residually-finite-minimal-actions-have-lef-full-groups: that imports LEF for full groups of residually finite minimal Cantor actions; this proves LEF for piecewise translations of tori with arbitrary real offsets and translations, whose actions need not be residually finite
---

**ESTABLISHED.** Identify `T^k = R^k/Z^k` with `[0, 1)^k` through coordinatewise
fractional parts `{x}`.
- A *basic set* is `{x ∈ [0, 1)^k : ⟨a_i, x⟩ ⋈_i b_i, i = 1, ..., s}` with `a_i ∈ Z^k`,
  `b_i ∈ R` and `⋈_i ∈ {<, <=, =}`. A *rational polyhedral set* is a finite union of basic
  sets.
- A *rational polytope exchange* of `T^k` is a bijection `g` of `[0, 1)^k` with a finite
  partition into rational polyhedral sets `P_1, ..., P_r` and vectors `t_1, ..., t_r ∈ R^k`
  such that `g(x) = {x + t_j}` on `P_j`. The offsets `b_i` and translations `t_j` are
  arbitrary reals. Only the normals `a_i` are required to be integer vectors.

**Statement.** Every finitely generated group of rational polytope exchanges of `T^k`, for
any `k >= 1`, is locally embeddable into finite groups (LEF).

**Examples covered.**
- `k = 1`: interval exchanges of the circle, recovering `interval-exchange-groups-are-lef`.
- Rectangle and box exchanges: every normal is `±e_i`.
- Polygon exchanges of `T^2` whose edges all have rational slopes.
- Full groups of free `Z^d`-subshifts coding a free toral rotation through a rational
  polyhedral partition embed in this group; see
  `fp-simple-groups-have-no-rational-polytope-exchange-action`.

**Mechanism.** This is rational specialisation, as for interval exchanges. Along an itinerary,
a word acts by an exact translation on a basic set with integer normals, and the offsets of
that set are integer affine forms in the parameters. Fourier–Motzkin elimination turns
nonemptiness of such sets into sign conditions on rational affine forms. Moving the
parameters to rationals with the same signs keeps every relation and non-relation of a ball.
At rational parameters the group permutes a finite grid.

**Model tests.**
- Labbé's partition `P_U` has the edge direction `(1, -φ)`
  (`labbe-shift-is-a-toral-rotation-coding`, item 6). Its normal is not proportional to an
  integer vector, so the claim does not apply, which matches the open
  `labbe-shift-derived-full-group-is-lef`.
- Thompson's `T` is finitely presented, infinite, simple and not LEF. Its elements have
  non-unit slopes, so they are not piecewise translations.

**Novelty.** None claimed. `research/artifacts/labbe-lef-2026-09-12.md`, Remark L4, records
that the interval exchange recipe "works when every sign condition is a `Q`-linear form in
the parameters, as for IETs and rectangle exchanges". This node states the class where that
holds for tori of every dimension and writes the proof out.

Route: `rational-polytope-exchange-groups-lef-proof`.
