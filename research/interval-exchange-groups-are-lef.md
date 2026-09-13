---
rg: 2
id: interval-exchange-groups-are-lef
kind: claim
title: Every finitely generated group of interval exchange transformations is LEF
distinct_from:
  labbe-shift-derived-full-group-is-lef: that asks whether one derived full group of a two-dimensional SFT is LEF, where rational perturbation of the toral polygon exchange fails; this proves LEF for one-dimensional interval exchanges, where rational specialisation works
  residually-finite-minimal-actions-have-lef-full-groups: that imports LEF for full groups of residually finite Cantor actions; this proves LEF for groups of interval exchanges with arbitrary real parameters, whose actions need not be residually finite
---

**ESTABLISHED.** An *interval exchange of the circle* `T = R/Z` is a bijection
`g : T -> T` for which there is a finite partition of `T` into half-open arcs
`[a_0, a_1), [a_1, a_2), ..., [a_(r-1), a_0 + 1)` such that `g` is a translation
`x -> x + t_j` on each arc. The breakpoints `a_j` and translations `t_j` are
arbitrary reals. Interval exchanges of `[0, 1)` are the special case of a circle
breakpoint at `0`.

**Statement.** Every finitely generated group of interval exchanges of `T` is locally
embeddable into finite groups (LEF).

**Mechanism: rational specialisation.** For words of length at most `2n` in the
generators, equality in the group is decided by the signs of finitely many affine
forms with integer coefficients in the breakpoints and translations of the
generators. Moving those parameters to rationals with the same signs gives
interval exchanges with rational parameters, which generate a finite group of
permutations of a grid, and the ball of radius `n` embeds there.

**Consequence.** `fp-simple-groups-have-no-interval-exchange-action`: no finitely
presented infinite simple group acts faithfully by interval exchanges.

**Model test.** Groups of interval exchanges contain `Z^d` and every finite group,
which are LEF. Thompson's `T` is finitely presented, infinite and simple, so it is
not LEF, and indeed it is not a group of interval exchanges: its elements have
non-unit slopes.

**Novelty.** None claimed. The rational-specialisation recipe for interval exchanges
is recorded as known in `research/artifacts/labbe-lef-2026-09-12.md` ("The IET
recipe"); this node writes the proof out.

Route: `interval-exchange-groups-are-lef-proof`.
