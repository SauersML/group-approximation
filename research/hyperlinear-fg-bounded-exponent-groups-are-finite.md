---
rg: 2
id: hyperlinear-fg-bounded-exponent-groups-are-finite
kind: claim
title: Every finitely generated hyperlinear group of finite exponent is finite
distinct_from:
  infinite-fg-bounded-exponent-groups-are-non-mf: that is the operator-norm MF form of the same finiteness principle, reduced to the corona restricted Burnside statement; this is the normalized Hilbert--Schmidt form, and neither implies the other on its face.
  hyperlinear-bounded-exponent-trace-rigidity-iff-finiteness: that is the established equivalence with a statement about limit traces of approximate exponent-N models; this is the finiteness statement itself.
---

**OPEN.** Let `G` be a finitely generated group of finite exponent. If `G` is
hyperlinear, then `G` is finite.

This is a Hilbert--Schmidt "Burnside problem". A proof would give a
non-hyperlinear group. The large odd exponent free Burnside groups are
infinite (`free-burnside-large-odd-exponent-is-nonamenable`), so they would be
non-hyperlinear, a negative answer to Weiss's Open question 9.4 in Pestov's
guide. Route: `non-hyperlinear-group-via-hyperlinear-burnside-finiteness`.

By `hyperlinear-bounded-exponent-trace-rigidity-iff-finiteness`, this
statement for `m`-generated groups of exponent dividing `N` is equivalent to
the following. Every limit trace of approximate exponent-N unitary models
factors through a finite quotient of `F_m`.

## Attempts

1. **Hilbert--Schmidt stability of exponent laws** (approach A5 of
   `research/artifacts/ideas-2026-09-13/nh/nh-small-cancellation.md`,
   2026-09-13).
   - Its trace-level conclusion is statement 2 of the equivalence node, so
     the route is this claim, not something weaker.
   - Rounding a single generator is free: move its eigenvalues to `N`-th roots
     of unity. Rounding does not pass to products, though, and at the trace
     level there is nothing left for stability to add.
2. **Kill test: an infinite f.g. hyperlinear group of finite exponent.** None
   found. The search below is not exhaustive.
   - Pestov, arXiv:0804.3968v8, §9, Open question 9.4 (text checked): "Is
     the free Burnside group of a finite exponent n sofic?" It is recorded
     there as open. A web search found no later answer.
   - Residually finite candidates die. A f.g. residually finite group of
     finite exponent embeds in a product of finite quotients of `R(m,N)`,
     hence is a quotient of `R(m,N)` and finite (`restricted-burnside-finiteness`).
   - Bounded-dimension approximations force LEF
     (`bounded-dimension-microstates-force-lef`). So a counterexample needs
     dimensions tending to infinity. An infinite bounded-exponent LEF group
     would be a counterexample. The MF analogue of that firewall is
     `bounded-exponent-lef-group-defeats-burnside-mf-program`.
   - Amenable groups are hyperlinear, so this claim forbids infinite f.g.
     amenable groups of finite exponent. A search summary called that
     existence question open; the source was not pinned against text.
3. **Calibration through stability.** By
   `hyperlinear-flexibly-hs-stable-group-is-residually-finite`, a flexibly
   HS-stable hyperlinear f.g. group of finite exponent is residually finite,
   hence finite. So flexible HS-stability of the bounded-exponent groups would
   prove this claim. Conversely, one infinite hyperlinear bounded-exponent
   group refutes every such stability principle for that group.
