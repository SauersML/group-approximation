---
rg: 2
id: order-seven-gauge-trivialization-selector-rank-proof
kind: route
title: One selector row with trivial gauge violates the affine rank equation
target: order-seven-gauge-trivialization-contradicts-selector-rank
requires:
  - two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
  - order-seven-moving-cuts-realize-both-affine-profiles
  - six-ungauged-moving-squares-lock-seven-gauges
  - six-exit-moving-cut-seventh-power-telescope
  - native-whitehead-hecke-head-has-order-seven-anchor
  - native-cross-gram-conclusions-fail-in-every-tracial-model
---

**Step 1 (trace identity).**  For an involution `D` put `P=(1-D)/2`, a
projection.  Then `(1-D)^2=2(1-D)`, so

```text
||1-D||_2^2 = tau((1-D)^2) = 2tau(1-D) = 4tau(P),
theta(D) = tau((1+D)/2) = 1 - ||1-D||_2^2/4.
```

**Step 2 (one row).**  By `(TSG1)` the negative fraction of
`C_q tensor D` is

```text
Phi_q(theta) = 1-q+(2q-1)theta = q - (2q-1)||1-D||_2^2/4.
```

So `|Phi_q(theta)-q| = |2q-1| ||1-D||_2^2/4`.  The inequality `(TSG3)` is
stated for one row with an arbitrary unitary `W` and an arbitrary
involution `V=D`, so it holds verbatim in any finite von Neumann algebra
(the proof there uses only traces of projections).  It gives
`|r-Phi_q(theta)| <= delta/2`.  The triangle inequality then yields
`(OGT1)`.  Substituting `(r,q)=(1/2,1/4)` gives `|2q-1|/4=1/8`, and
multiplying by 2 gives `(OGT2)`.  Substituting `(1/4,1/8)` gives
`|2q-1|/4=3/16`, and multiplying by 2 gives `(OGT3)`.  Using
`(TSG8)` `delta^2>=4|r-Phi|` in place of `(TSG3)` gives `(OGT4)`.

**Step 3 (tightness).**  In the exact model
`order-seven-moving-cuts-realize-both-affine-profiles`, the rows are exact
(`delta=0`) with `theta(D_1)=1/2` and `theta(D_2)=5/6`.  Step 1 gives
`||1-D_1||^2=2` and `||1-D_2||^2=2/3`, and then `(OGT2)` and `(OGT3)` hold
with equality.  The verifier
`experiments/order-seven-gauge-kill-2026-09-17/verify_trivial_gauge_rank_floor.py`
checks Step 1 and `(OGT1)` on 400 random Haar and involution instances,
checks tightness in exact rational arithmetic, and realizes the two OAP
tensor dimensions.

**Step 4 (GMI).**  In GMI the cut `E_0` must retain row `i` with
multiplicity involution `D_i`, so `delta_i=o(1)`.  The conclusion of
`(GMC3)` is `||1-D_i||_2=o(1)`.  Then the left side of `(OGT2)` (resp.
`(OGT3)`) is `o(1)`, a contradiction.  This happens in every model, so no
model satisfies the conclusion of GMI.

**Step 5 (ESB).**  Suppose the six-bridge interface gives `(ESB1)--(ESB3)`
with errors `o_2(1)`.  Then `(SGL5)` gives
`||D_(i,k)-D_(i,0)||_2=o(1)` for all `k`.  The six-exit telescope and the
order-seven anchor give `(SGL6)` with `rho=o(1)`; this is exactly the
computation `(GMC8)` of the route `six-moving-squares-give-el20-multicut`.
Then `(SGL7)` and `D_(i,0)^2=1` give `||D_(i,0)-1||_2=o(1)`.  The cut
`E_0` of the interface is the GMI source, which carries row `i` with gauge
`D_(i,0)` (hypothesis (H), `(OAP4)`).  Step 4 then applies.

**Step 6 (word searches).**  All ESB errors are charged to a fixed finite
relator menu with dimension-free constants.  In an exact representation
into a finite von Neumann algebra those defects vanish, so the estimates
become exact identities.  If the construction of `E_0` and its rows is
valid there, as recorded for the native packets in Step 1 of
`native-cross-gram-conclusions-fail-in-every-tracial-model`, then Step 5
gives `D_(i,0)=1` exactly while `delta_i=0`.  This contradicts `(OGT2)`.
Hence no such relator-charged word exists.  If instead the construction is
not valid in exact tracial models, then (H) or the E_0 construction uses
non-tracial input.  That is the other branch of the stated dichotomy.  In
that branch the downstream route
`order-seven-growing-multicut-gives-el20-native-cross-gram` inherits the
cross-Gram class kill.

No Property `(T)`, Kazhdan input or new literature theorem is used.
