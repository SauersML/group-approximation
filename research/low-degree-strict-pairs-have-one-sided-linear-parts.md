---
rg: 2
id: low-degree-strict-pairs-have-one-sided-linear-parts
kind: claim
title: The linear parts of a low-degree injective automaton and its decoder over F_q form a one-sided inverse pair over the group algebra
distinct_from:
  invariant-output-automata-have-only-nonlinear-decoders: that assumes a linear decoder over F_2 and an arbitrary encoder; this allows nonlinear decoders over any F_q and compares linear parts under the bound deg sigma * deg tau < q, where the reduction x^q = x cannot reach degree one.
  certificate-linear-automata-have-local-linear-decoders: that builds linear decoders for certificate-linear encoders; this extracts a one-sided inverse pair from the linear parts of an arbitrary low-degree polynomial pair and puts the remainder in unipotent normal form.
  stable-finiteness-failure-refutes-surjunctivity: that turns a one-sided inverse pair into a strict linear automaton; this goes the other way, from a low-degree nonlinear strict pair to a pair or a unipotent automaton.
artifacts:
  - research/artifacts/low-degree-strict-pairs-linear-parts-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `F = F_q`, `q = p^k`, `G` any group, and let `tau`, `sigma` be automata over the
alphabet `F^m`. Normalize them by translation so that `tau(0) = 0`. Suppose
`sigma tau = id` and `deg sigma * deg tau < q`, where degree means the total degree of
the reduced polynomial local rule. Let `A, C in M_m(F[G])` be the linear parts. Then
`C A = I_m`.

**Dichotomy.**
- If `A C != I_m`, then `M_m(F[G])` is not directly finite and `tau_A` is a strict linear
  automaton, over `F_p` at matrix size `mk` by restriction of scalars.
- If `A C = I_m`, then `tau_C tau = id + (terms of degree >= 2)` is strict exactly when
  `tau` is, and it keeps the degree bound: the unipotent normal form.

**Why.** Substituting the encoder into a decoder monomial of total degree `D` gives
monomials whose total degree lies in `[D, D deg tau]`, with every exponent below `q`. So
nothing reduces, and degree one comes only from `D = 1`.

**Scope, needed.** On `F_8`, `tau = x^3` and `sigma = y^5` satisfy `sigma tau = id` with
zero linear parts. There the reduction `x^8 = x` feeds degree 15 into degree one. Over
`F_2` the bound forces both maps linear, so this claim says nothing about genuinely
nonlinear binary designs.

Proof: Sections 1, 2 and 4 of the artifact.
