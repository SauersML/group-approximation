---
rg: 2
id: noise-test-transparent-on-decodable-matching-features
kind: claim
title: The folded long-code noise test is no sounder than the game split along any decodable matching feature
distinct_from:
  bkm-test-transparent-on-learnable-games: that needs the whole edge matching to be decodable; this needs only a decodable coarse feature of it, and interpolates between the derived unique game (full decoding) and the dictator bound (no decoding).
  separated-small-pairing-families-defeat-the-noise-test: that constructs explicit low-value separated-family instances; this is a per-instance lower bound for every 2-to-1 game and every decodable partition of its matchings.
artifacts:
  - research/artifacts/unique-games-smooth-design-learnability-2026-09-11.md
---

**ESTABLISHED.** Let `Psi` be a regular 2-to-1 game with left alphabet `[2n]`
and right alphabet `[n]`. Let `R_(rho,m)` be the folded long-code noise test of
Braverman--Khot--Minzer (ITCS 2021, Section 5).

At each left vertex `u`, partition the matchings occurring at `u` into
classes, and let `D_u` be a shift-invariant decoder of the class from one
noisy pullback, with worst-case error `e_c`. The coarsened game `Psi_c` splits
`u` into one vertex `(u,K)` per class. It keeps the alphabet `[2n]` and every
constraint, so `val(Psi) <= val(Psi_c) <= val(UG_der(Psi))`. Then

```text
val(R_(rho,m)(Psi)) >= 1/m + (1-1/m) rho^3 val(Psi_c)^2 - 2 e_c.
```

The identity partition gives the derived unique game bound. The one-class
partition gives the dictator bound `1/m + (1-1/m) rho^3 val(Psi)^2`.

**Consequence.** If the test is sound on NO instances
(`val(R(Psi)) <= epsilon`), then for every decodable feature

```text
val(Psi_c) <= sqrt((epsilon + 2 e_c) / ((1-1/m) rho^3)).
```

Hardness through the test must survive splitting each left vertex along every
feature the noisy pullback reveals, even when the matching itself cannot be
learned. So an enrichment of learnable hard instances that keeps an ancestral
feature recoverable, such as the affine direction, gains soundness only if the
game split along that feature is already hard. No hardness, algorithm, or
status of UGC is asserted.

DERIVATION noise-test-decodable-feature-transparency-proof
