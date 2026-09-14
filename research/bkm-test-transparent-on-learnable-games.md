---
rg: 2
id: bkm-test-transparent-on-learnable-games
kind: claim
title: On learnable 2-to-1 instances the folded long-code noise test adds no soundness beyond a derived unique game
invalidates:
  - ugc-via-bkm-test-on-learnable-hardness
distinct_from:
  affine-long-code-test-has-no-uniform-soundness: that is the explicit low-value affine instance sent to a high-value output; this draws the reduction-level consequences of the derived-unique-game bound -- distinct-matching collapse, transparency of any reduction through the test, and the necessary vanishing of the derived unique game value.
  dummy-padding-cannot-beat-the-random-guessing-floor: that is the alphabet-sized-list floor for one dead richness attack; this is the general statement that the long-code layer is transparent whenever the derived unique game has bounded value.
  separated-small-pairing-families-defeat-the-noise-test: that constructs explicit low-value separated-family instances with high output value; this is the reduction-level corollary about what any test-based route to UGC must supply.
artifacts:
  - research/artifacts/unique-games-bkm-test-transparency-2026-09-11.md
---

**ESTABLISHED.** Consequences of
`derived-unique-game-lower-bounds-the-noise-test`, writing `UG_der` for the
derived unique game and `e(Psi)` for its decoder-error term.

1. **Distinct matchings collapse.** If at every left vertex of `Psi` the
   incident edges carry pairwise distinct matchings, then
   `val(UG_der(Psi))=1`, so
   `val(R_(rho,m)(Psi)) >= 1/m+(1-1/m)rho^3-2e(Psi)` **whatever `val(Psi)` is.**
   `F_lin` on `GF(2)^k` is this case with `delta=1`, `|F_u|<=2n-1`.

2. **Transparency.** Suppose a polynomial-time reduction from an NP-hard
   problem outputs 2-to-1 games with `val(Psi)>=1-eta` on YES instances,
   `val(R_(rho,m)(Psi))<=epsilon` on NO instances, and `e(Psi)<=xi`
   throughout. Then `Psi -> UG_der(Psi)` is itself a polynomial-time reduction
   proving `Gap-Unique_n[1-eta, s]` is NP-hard, with
   `s = sqrt((epsilon+2xi)/((1-1/m)rho^3))`. So any hardness proof that routes
   through the test on such instances already contains a direct proof of unique
   games hardness, with constant alphabet `n` and no long code.

3. **Necessary condition.** BKM's soundness implication for the test
   (`val(Psi)<=eta => val(R(Psi))<=epsilon`, small `epsilon`) can hold on a
   learnable family only where `val(UG_der(Psi)) -> 0`; equivalently the
   matching classes at a typical left vertex must have unbounded multiplicity.

"Learnable" means the per-vertex matching family `F_u` is decodable from one
noisy pullback table, i.e. `e(Psi)=o(1)`, which by
`separated-pairing-families-admit-noisy-decoders` holds whenever `|F_u|` is
subexponential in `n` and the family is `delta_0`-separated for a fixed
`delta_0>0`. The claim does not decide UGC; it constrains how a test-based
route could reach it. No hardness or algorithm is asserted.

DERIVATION bkm-test-transparency-proof
