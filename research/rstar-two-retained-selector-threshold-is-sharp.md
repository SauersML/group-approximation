---
rg: 2
id: rstar-two-retained-selector-threshold-is-sharp
kind: claim
title: Retaining three full-support R-star coordinates leaves no local cap-selector freedom
distinct_from:
  rstar-two-retained-coordinates-admit-a-fixed-cap-section: that proves universal cap completion with at most two retained coordinates; this proves the threshold cannot be increased to three.
  extreme-traces-and-local-pruning-do-not-select-fano-caps: that gives a factorial global counterexample to extremal-trace selection; this is the elementary single-row obstruction to fiberwise generator replacement.
---

**ESTABLISHED.**  For every set `K` of three coordinate positions, the
projection

```text
R_* -> F_2^K                                               (RTS1)
```

is injective and has seven-point image.  Indeed odd parity uniquely recovers
the omitted bit, and deleting the ghost deletes exactly one projected
pattern.  Hence, in the faithful abelian representation `C^7` of one `R_*`
row, retaining the three observables in `K` forces the fourth observable on
every joint spectral atom.  Any replacement which keeps the full `R_*`
predicate is the original fourth observable.

The resulting support remains all seven Fano points and is not a cap.  Thus
no model-independent fiberwise selector can retain three arbitrary
full-support coordinates.  The two-tail peeling kernel is precisely the
place where local deterministic replacement loses all guaranteed freedom.

