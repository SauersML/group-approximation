---
rg: 2
id: own-block-local-bijection-rows-peel
kind: claim
title: An own-block row that is a local bijection peels like a type-(O) step, even when nonlinear
distinct_from:
  controlled-self-linear-feedback-ca-are-surjunctive: that peels rows whose own part is a bijective linear automaton; this peels any own-block row whose self-map is a bijection for every value of the other blocks, linearity dropped, and only reduces to a corrected tail rather than concluding surjectivity.
  nonlinear-certificate-fibers-are-all-surjective-or-all-strict: that is the fiber dichotomy for a certificate-fixing finite-memory map; this is the peeling step for one own-block row built on top of it, identifying bijectivity of the own-block self-map as the exact peelability condition.
artifacts:
  - research/artifacts/corrected-tail-peeling-boundary-2026-09-12.md
---

Let `F` be an injective cellular automaton on blocks `X, Y` over a group `G` and
a finite ring `R`, whose `X`-rows form an **own-block local-bijection row**: for
every configuration `Y` the self-map `Phi_Y : X -> row(X,Y)` of the block-`X`
full shift is a bijection. Its inverse is then automatically local, uniformly in
`Y`, by Curtis--Hedlund--Lyndon applied to `(X,Y) -> (Phi_Y(X), Y)`. Linearity is
not assumed. Let `X^*(Y) = Phi_Y^{-1}(0)` be the correction and `F'` the `Y`-rows
of `F` evaluated at `(X^*(Y), Y)`.

Then `F'` is injective, `F` is surjective iff `F'` is surjective, and if `F'` is
surjective then so is `F`.

This extends the type-(O) peeling step of
`controlled-self-linear-feedback-ca-are-surjunctive` from a bijective linear
`L_Y` to any own-block bijection. Instances:
- composites of track shears `(u,v) -> (u + f(v,Y), v)` and
  `(u,v) -> (u, v + h(u,Y))` inside the block. These also peel track by track
  with type-(O) steps;
- the single-track order-three control `x(h) + x(h)x(ht) + x(ht)x(ht^2)` over
  `F_2`, with `t` of order three. It permutes `F_2^3` on each left coset of `<t>`,
  is nonlinear, and cannot be split into tracks, so it is a genuine case beyond
  type (O).

## Attempts

Proved in Section 1 of the artifact via
`nonlinear-certificate-fibers-are-all-surjective-or-all-strict`: `E(X,Y) =
(Phi_Y(X), Y)` is a bijective cellular automaton fixing the certificate `Y`, so
`F = (F o E^{-1}) o E` with `F o E^{-1}` certificate-fixing and injective; the
fiber dichotomy gives the corrected-tail equivalence. Established by the
companion route.

**Correction 2026-09-12** (gk-vf-positive, Section 7.1 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`). The peeling lemma passes. The "sufficient nonlinear instance" is withdrawn. For nonlinear `N_Y`, `sum_(k<D) (-N_Y)^(k)` is not an inverse of `X + N_Y(X)`, even when `N_Y o N_Y = 0`, because `(I+N)(x - N(x)) = x - N(x) + N(x - N(x))`. The artifact example `x(g) + x(g+1)x(g+2)` over `F_2` is not injective: both constant configurations map to `0`. Valid nonlinear instances are composites of track shears inside the block, `(u,v) -> (u + f(v,Y), v)` and `(u,v) -> (u, v + h(u,Y))` with arbitrary local `f` and `h`, whose inverses are the opposite shears. The "uniformly bounded local inverse" hypothesis is automatic once every `Phi_Y` is bijective.

**Resolved 2026-09-12** (gk-p-tails). The withdrawn instance has been removed from the statement above and from Section 1 of the artifact. It is replaced by the track shears and by the single-track order-three control, whose bijectivity is checked there. The local-inverse hypothesis is dropped as automatic.
