---
rg: 2
id: packet-hard-transport-preserves-pulse-prefix
kind: claim
title: Transport each forbidden packet exit inside the previously positive pulse prefix
distinct_from:
  commuting-pulse-prefix-cuts-form-summable-first-hit-reservoir: that makes prefix preservation the single leakage term in `(PCF3)`; this must bound that term from finite group relators.
  product-clock-synchronizes-fanizza-and-e5: that conjugates the current hard word to the current pulse; this must simultaneously intertwine every earlier positive pulse sign.
  e5-tail-character-suppression-for-projected-exits: that is the resulting first-hit conclusion; this is its exact word-level transport obligation.
---

Let `B_k` be the commuting E5 pulse involutions and

```text
C_n=product_(k<n)(I+B_k)/2.
```

For the forbidden packet exit projection `P_n` and its hard-sign transport
word `V_n`, construct a finite presentation and polynomial `p` such that

```text
||(I-C_n)V_nP_n||_2^2 <= p(n) E_local+o(1).           (PHP1)
```

The current hard covariance already gives the other term in `(PCF3)`.  Thus
`(PHP1)` is precisely what turns negative pulse mass into a new first-hit
exit.

## Attempts

- A single HNN relation `vA_0v^-1=B_0` transports the current sign after
  conjugation, but it does not make `V_n` preserve the earlier `B_k` signs.
  Persistent-tail mass may therefore re-enter old layers.
- Making the E5 factor commute with the BCS factor gives prefix carriers that
  reduce all BCS words, but an HNN transport between the factors need not
  preserve those carriers.
- The next finite-presentation ansatz is to put `v` in the centralizer of a
  one-sided negative pulse module whose conjugates exhaust the earlier signs.
  This requires a genuine ascending centralizer, not a bilateral polynomial
  clock.
