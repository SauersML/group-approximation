---
rg: 2
id: hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
kind: claim
title: A countable group is hyperlinear iff its group factor embeds in the hyperfinite ultrapower iff it has matrix microstates with vanishing traces
distinct_from:
  hnn-hyperlinearity-is-amalgamated-free-haar-unitary: that applies this equivalence to the HNN group and characterizes the extension of an embedding of the base; this is the bare literature equivalence itself, isolated so that routes which convert "hyperlinear" into "microstates with trace tending to delta_e" can cite it.
  non-hyperlinear-group: that is the goal; this is the standard dictionary between its three equivalent formulations.
---

**Literature input.**  For a countable discrete group `G` the following
are equivalent:

1. `G` is hyperlinear: `G` embeds in the unitary group of a tracial
   ultraproduct of matrix algebras `R^U = prod_U M_(d_n)` (equivalently of
   the hyperfinite II_1 factor's ultrapower) as a subgroup, with the
   ultraproduct of the normalized Hilbert--Schmidt metrics.
2. The group von Neumann algebra `L(G)` embeds trace-preservingly into
   `R^U` (equivalently, `L(G)` is Connes-embeddable).
3. There are maps `U_n : G -> U(d_n)` with
   `|| U_n(g) U_n(h) - U_n(gh) ||_2 -> 0` for all `g, h in G` and
   `tr_(d_n) U_n(g) -> delta_(g,e)` for all `g` (normalized trace):
   microstates for the regular trace.

**Sources.**  (1) ⟺ (2) is F. Rădulescu, *The von Neumann algebra of the
non-residually finite Baumslag group `<a,b | a b^3 a^(-1) = b^2>` embeds
into `R^omega`*, in: Hot topics in operator theory, Theta Ser. Adv. Math.
9 (2008), 173--185 (arXiv:math/0004172), where hyperlinearity is defined
and shown equivalent to the embedding of `L(G)`; see also V. Pestov,
*Hyperlinear and sofic groups: a brief guide*, Bull. Symbolic Logic 14
(2008), Section 5.  (2) ⟺ (3) is the standard unwinding of a
trace-preserving embedding through representing sequences, recorded in
the route.

**Use.**  Every route in this graph that passes from "`G` is hyperlinear"
to "there are almost-multiplicative matrix tuples with
`tr U_n(w) -> 0` for `w != e`" (for instance the HNN theorem
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear`, whose contradiction
is exactly `tr -> 1` against `tr -> 0`) consumes direction (1) ⟹ (3);
every route that builds a non-hyperlinear group from a non-Connes-embeddable
subalgebra of `L(G)` consumes (2) ⟹ (1).
