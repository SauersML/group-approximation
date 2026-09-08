---
rg: 2
id: iwahori-second-order-repair-space-is-empty
kind: claim
title: At every compatible Iwahori pair the projected second-order form vanishes on the whole neutral space
distinct_from:
  iwahori-uniform-infinitesimal-rigidity: that is the uniform lower bound on the nonzero part of the mismatch map, a statement about the size of its first-order image; this identifies the kernel as integrable and concludes that its second-order contribution is exactly zero.
  normalized-hs-taylor-remainder-is-not-dimension-free: that shows the second-order remainder has no dimension-free bound in normalized HS, killing a Newton route; this shows the second-order term is identically zero in the one place a stress-correction argument would want it to be large.
  integrable-neutral-directions-pay-no-second-order: that is the general screen for any C^2 residual map; this is its evaluation at the Dogon-Vigdorovich mismatch map, using uniform infinitesimal rigidity to prove the hypothesis of that screen holds there.
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

**ESTABLISHED.**  Work in the chart of `iwahori-local-global-defect-question`:
a pair `pi = (pi_+, pi_-)` of unitary representations of the two modular vertex
groups `V_1, V_2` on `C^d`, with residual

```text
F(pi) = ( pi_+(s) - pi_-(sigma s) )_(s in S_B),
```

whose norm is the local defect `def(pi)`.  Each `V_i` is an amalgam of finite
groups, so its unitary representation variety is smooth and the admissible
directions at `pi` are exactly the pairs of anti-Hermitian cocycles
`(c_1, c_2) in Z^1(V_1, Ad rho) (+) Z^1(V_2, Ad rho)`, with
`DF(pi)[c_1, c_2] : b -> c_1(b) - c_2(sigma b)`.

Let `pi` be compatible, i.e. `pi = rho|_(V_1), rho|_(V_2)` for a representation
`rho` of `SL_2(Z[1/2])`; by the congruence subgroup property `rho` is a
congruence representation, so `(UIR)` of `iwahori-uniform-infinitesimal-rigidity`
applies.  Then:

1. `ker DF(pi)` is exactly the diagonal coboundaries `{(delta x, delta x)}`
   -- this is `(UIR)` at linearized defect zero.
2. Every such direction is integrable: `t -> (Ad(exp t x) pi_+, Ad(exp t x) pi_-)`
   is a curve of *compatible* pairs with that derivative, because conjugating
   both members by the same unitary preserves `pi_+|_B = pi_- o sigma`.
3. Hence, by `integrable-neutral-directions-pay-no-second-order`,

```text
Pi D^2F(pi)[xi, xi] = 0    for every xi in ker DF(pi).                  (E1)
```

The same holds after padding by any compatible block: `rho (+) rho'` with `rho'`
a representation of `SL_2(Z[1/2])` is again compatible and congruence, so
`(UIR)` and therefore `(E1)` apply verbatim to the padded pair.

**Consequence for the stress-correction transfer.**  The mechanism of
`second-order-step-beats-a-blocked-linearization` requires a neutral direction
whose projected quadratic term is comparable to the blocked residual.  By `(E1)`
no such direction exists at any compatible pair, and by continuity of `D^2F` the
form is small on neutral directions at nearby pairs.  So a quadratic repair
argument for this question cannot draw its directions from the compatible locus,
nor manufacture them by padding with compatible blocks; it must operate at pairs
bounded away from that locus, where `ker DF` has no cohomological description.
That is the noncongruence far sector of `iwahori-outlier-repair`.

This claim refutes one attack template.  It says nothing about the answer to
`iwahori-local-global-defect-question` itself, and nothing about padding by
blocks that are not compatible, which moves the base point off the locus where
`(UIR)` is available.
