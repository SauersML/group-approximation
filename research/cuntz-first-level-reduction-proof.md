---
rg: 2
id: cuntz-first-level-reduction-proof
kind: route
title: Apply cyclic trace internally and Julia reflections externally
target: cuntz-first-hit-checksum-is-a-one-scale-corner
requires:
  - approximate-relative-leavitt-cell-kills-active-trace
  - even-partial-swap-star-has-canonical-trace-floor
---

For the internal case, cyclicity gives

```text
tau(S_iS_i^*)=tau(S_i^*S_i).
```

The two initial equations place the sum near `2tau(Q)`, whereas the range
sum places it near `tau(Q)`.  The normalized trace is bounded by normalized
Hilbert--Schmidt norm, yielding `(CFC3)` exactly as in the relative Leavitt
trace lemma.

For the external case, the initial projections coincide and the final
projections are orthogonal.  Complete each partial isometry to its Julia
involution.  The binary instance of the partial-swap-star trace formula gives
the fixed one-scale word-trace floor.  Neither calculation uses any deeper
prefix.

