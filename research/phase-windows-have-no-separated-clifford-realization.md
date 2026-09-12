---
rg: 2
id: phase-windows-have-no-separated-clifford-realization
kind: claim
title: A table carrying the Kun--Thom phase has no coordinate realization in a Clifford cover with separable edges, over any base group
distinct_from:
  clifford-cover-strict-pairs-read-invisible-adjacency: that is a necessary condition on strict pairs over one cover, proved by re-choosing the graph over the same base; this says a phase-carrying table realizes coordinate-wise in no Clifford cover with profinitely separable edges, over any base group and site set.
  kun-thom-clifford-radical-phase: that computes the exact Clifford phase of the radical word; this shows every window carrying that phase blocks coordinate transport into separated or saturated covers.
  profinitely-saturated-clifford-covers-are-surjunctive: that proves saturated covers surjunctive by coordinate transport; this shows no coordinate transport carries a phase window into a cover with separable edges.
artifacts:
  - research/artifacts/clifford-cover-phase-barrier-2026-09-12.md
---

**Setting** (artifact Section 0).
- `(F, P)` is a finite partial multiplication table in a Clifford cover `E_S`.
- A *coordinate realization* in another Clifford cover `E_(S')(Y)` over a group `G'` is
  `phi(u, s, g) = (lambda u, s, psi(g))`. Here `lambda` is injective on the read sites and equivariant for the
  table's moves, and `phi` is multiplicative on `P`, sign included.
- The realization *sees phase data* at a read site `x_0` when:
  - group parts `b_i` fix `x_0` through moves;
  - `psi(t) B' psi(t)^(-1) <= B' = <psi(b_i)>`, and `psi(h) = psi(t)^(-1) psi(b) psi(t)` with `psi(b) in B'`;
  - a move sends `x_0` to `h x_0 != x_0`;
  - both products `c_(x_0) c_(h x_0)` and `c_(h x_0) c_(x_0)` are read, and `{x_0, h x_0}` is an edge of `S`.

**Theorem.** Then `lambda(x_0)` and `lambda(h x_0)` are distinct, adjacent in `S'`, and not separated by any
finite quotient `K\Y`. So `S'` is neither a finite pullback nor profinitely saturated.

**Kun--Thom instance.** For the Theorem E pair and any graph containing the phase edge `{o, h o}` (the complete
graph included), take the table made of `c_o`, `c_(h o)`, `eps`, generators of `Gamma`, `t`, `t^(-1)`, `gamma`
and `h`. Its products express:
- `Gamma` fixing `o`;
- the ascending relations `t b_i t^(-1) = w_i(b)`;
- `h = t^(-1) gamma t` and `h c_o = c_(h o) h`;
- `c_o c_(h o) = eps c_(h o) c_o`.

This table has no coordinate realization in any Clifford cover, over any group, whose edges are all
profinitely separable.

**Consequence.** The saturation method (`profinitely-saturated-clifford-covers-are-surjunctive`) cannot reach any
window that carries the phase, even after changing the base group, site set or graph. Finite targets were
already excluded by Theorem B''.

**ESTABLISHED** by `phase-windows-no-separated-clifford-realization-proof` (artifact Section 1). Proved on paper
by lane w4-clifford-complete; independent re-derivation requested from w3-vf-nonlinear.
