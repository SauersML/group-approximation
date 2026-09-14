---
rg: 2
id: formal-polynomial-strict-pairs-need-unstable-linearization
kind: claim
title: A left-inverse identity that holds formally forces bijectivity once the matrix group algebra is directly finite
distinct_from:
  certificate-linear-automata-have-local-linear-decoders: that concerns automata linear in the data under local certificate control and produces linear decoders; this concerns arbitrary polynomial automata whose left-inverse identity is a polynomial identity, linearized at a constant configuration.
  invariant-output-automata-have-only-nonlinear-decoders: that excludes linear decoders for automata with invariant output; this shows every formally left-invertible polynomial pair is bijective once the matrix group algebra is directly finite.
  triangular-forward-tables-force-surjectivity: that is a condition on product coincidences making the table group free; this is a condition on how the left-inverse identity uses the arithmetic of the alphabet, with no hypothesis on the table.
  low-degree-strict-pairs-have-one-sided-linear-parts: that extracts one-sided linear parts under deg sigma * deg tau < q and leaves a unipotent branch; this assumes only that the identity is formal for some representatives and concludes bijectivity outright under direct finiteness, so that degree bound is one sufficient condition for its hypothesis.
  unipotent-automata-over-finite-fields-are-surjective: that proves surjectivity for invertible linear part and a degree-bounded decoder, by injectivity of the pullback on the polynomial ring; this proves two-sided formal invertibility for any formal left-inverse identity under direct finiteness, by the formal inverse function theorem, with no degree bound.
  low-degree-strict-automata-force-matrix-kaplansky-failure: that is the degree-bounded strict case; this is the general formal case, where formality may come from a degree bound, disjoint decoder footprints or an infinite field.
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `G` be a group, `k` a field, `n >= 1`, and let `tau`, `sigma` be polynomial automata on
`(k^n)^G`, meaning finite memories and polynomial local rules. Suppose `sigma o tau = id` holds as a
formal polynomial identity in the variables `X_(h,i)`, `h in G`. Products of memory addresses are
computed in `G`, so the identity may use coincidences of products, but over a finite field it may not
use `x^q = x`.

If `M_n(k[G])` is directly finite, then `tau o sigma = id` formally, and `tau` is bijective.

**Proof idea.**
- Linearize at a constant configuration: the chain rule gives `J_sigma J_tau = 1` in `M_n(k[G])`.
- Direct finiteness makes `J_tau` invertible.
- Finite-memory formal maps with invertible linear part are units of the composition monoid, so
  `sigma` is the two-sided formal inverse of `tau`.

**Consequences.**
- **Infinite fields.** A functional identity is formal. So a strict polynomial pair over an infinite
  field of characteristic `p` forces a one-sided inverse pair in `M_n(k[G])`, and hence `F_p[G]` not
  stably finite.
- **Characteristic 0.** Kaplansky's theorem makes polynomial automata with a polynomial left-inverse
  automaton bijective over every group.
- **Screen for nonlinear designs.** On a group whose prime-field group algebra is stably finite, the
  following are bijective: shears, triangular circuits, Nagata-type designs, anything specialized
  from polynomial identities over infinite fields or `F_p[t]`, low-degree pairs, and decoders with
  disjoint encoder footprints (`disjoint-footprint-decoders-force-kaplansky-failure`). A nonlinear
  counterexample there must be a non-formalizable pair (artifact, Section 6).

Verified by gk-vf-nonlinear (Section 7 of its verification artifact, PASS). This is the first result
of lane gk-free-neg ("the arithmetic of the alphabet"); Section 0 of the artifact explains the choice.
