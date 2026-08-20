---
rg: 2
id: gauge-doubling-selector-flip-proof
kind: route
title: Push joint spectra through parity and covariantize by the finite gauge orbit
target: gauge-doubling-gives-selector-flip-symmetries
requires: []
---

Given a solution of `B`, set `A_x=X_x` and `B_x=1`. Conversely, from a
solution of `G(B)` set `X_x=A_xB_x`. The lifted context makes all factors
commute, so the products are involutions, commute in the original contexts,
and their joint spectral assignments are exactly the parity images of the
share assignments. This proves every satisfiability equivalence.

The same two substitutions define unital star homomorphisms between the two
universal BCS algebras. Their composite on the original algebra is the
identity, proving injectivity and signal preservation.

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

