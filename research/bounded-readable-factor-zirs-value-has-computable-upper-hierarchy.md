---
rg: 2
id: bounded-readable-factor-zirs-value-has-computable-upper-hierarchy
kind: claim
title: A fixed readable-factor atom bound has a computable decreasing ZPC-IRS value hierarchy
distinct_from:
  zpc-irs-value-computable-upper-hierarchy: that treats all ZPC-IRS strategies; this retains only strategies whose full readable translate algebra has at most a prescribed number of atoms.
  perfect-gap-zpc-has-finite-readable-translate-algebra: that asks for some finite bound on a perfect gap witness without supplying the bound; this proves effective compactness after an integer bound is fixed.
  bcv-halt-readable-finite-orbit-does-not-transfer-to-gap-irs: that separates the finite HALT models from the unrestricted NONHALT compactness witness; this makes a uniform computable HALT-side atom bound usable in a new restricted diagonalization.
---

Let `G` be a finite tailored game and let `B>=1` be an integer.  Restrict
ZPC-IRS strategies to those for which the full readable translate algebra

```text
D_infinity = W*( pi(g) D_0 pi(g)^* : g in Q_G )
```

has at most `B` atoms.  Write the resulting value as
`omega_ZIRS^B(G)`.  There is a computable decreasing sequence of rational
numbers

```text
alpha_(1,B)(G) >= alpha_(2,B)(G) >= ...
                    -> omega_ZIRS^B(G).                 (BRH1)
```

The restricted value is a maximum, not merely a supremum.

The bound in this statement is the number of atoms, equivalently the
dimension, of the whole invariant Boolean algebra.  A bound `K` only on the
number of distinct translates of `D_0` can be converted to the atom bound

```text
B <= 2^( |S_R| K ),
```

where `S_R` is the finite set of readable bits.  No finite-dimensional
bound is placed on the IRS fibers or on the stabilizer-character GNS algebra.
