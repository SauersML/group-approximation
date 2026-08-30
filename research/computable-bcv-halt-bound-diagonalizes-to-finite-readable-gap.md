---
rg: 2
id: computable-bcv-halt-bound-diagonalizes-to-finite-readable-gap
kind: claim
title: A computable BCV HALT readable bound diagonalizes to a finite-readable NONHALT gap
distinct_from:
  perfect-zpc-irs-quantum-gap-game: that diagonalizes the unrestricted ZPC-IRS value and obtains no orbit bound; this diagonalizes the bounded-factor value using a bound already computable from the machine description.
  bcv-halt-completeness-has-computable-readable-factor-bound: that is the unproved uniformity premise; this proves what the premise would imply.
  perfect-gap-zpc-has-finite-readable-translate-algebra: that directly asks for a finite-factor gap witness; this supplies one conditionally and with an explicit per-instance atom bound.
---

Assume there is a total computable function `B(M)`, independent of the
halting time, such that every halting machine's BCV game `G_M` has a perfect
ZPC strategy with

```text
dim D_infinity <= B(M).                                  (CBD1)
```

Then some nonhalting machine `M_0` has an actual ZPC-IRS strategy satisfying

```text
omega_ZIRS^(B(M_0))(G_(M_0)) = 1,
omega*(G_(M_0)) <= 1/2,
dim D_infinity <= B(M_0).                                (CBD2)
```

In particular, a halt-time-independent computable readable-factor bound on
BCV perfect completeness is sufficient to produce the finite-readable
perfect quantum gap needed by
`finite-readable-translate-algebra-groupifies-zpc-gap`.
