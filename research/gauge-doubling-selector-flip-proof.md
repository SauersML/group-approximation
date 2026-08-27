---
rg: 2
id: gauge-doubling-selector-flip-proof
kind: route
title: Push joint spectra through parity and covariantize by the finite gauge orbit
target: gauge-doubling-gives-selector-flip-symmetries
requires: []
---

Given a solution of `B`, set `A_(c,x)=X_x` and `B_(c,x)=1` for every
incidence. Conversely, the defining product relations in a solution of
`G(B)` recover the retained `X_x`. The lifted context makes all factors
commute, so the products are involutions, commute in the original contexts,
and their joint spectral assignments are exactly the parity images of the
share assignments. This proves every satisfiability equivalence.

The inclusion of the retained logical variables and the substitution sending
each occurrence pair to `(X_x,1)` define unital star homomorphisms whose
composite on the original algebra is the identity, proving injectivity and
signal preservation.

Flipping both shares changes neither their product nor any lifted truth-table
condition. The flips have disjoint supports on the generating set and hence
commute. For a representation `pi`, the direct sum of all gauge twists is
permuted by the left regular action of the gauge group, giving `(GDB3)`; a
logical signal is fixed on every summand.

Finally, for approximate unitaries, repeated use of

```text
||UV-U'V'||_2 <= ||U-U'||_2+||V-V'||_2
```

and the analogous commutator telescoping estimate gives a constant depending
only on the finite incidence of `B`. No dimension or runtime enters.
