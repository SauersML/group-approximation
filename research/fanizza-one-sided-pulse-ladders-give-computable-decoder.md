---
rg: 2
id: fanizza-one-sided-pulse-ladders-give-computable-decoder
kind: claim
title: One-sided pulse ladders give the finite Fanizza BCS a computable matrix decoder
distinct_from:
  relative-rank-one-fanizza-groupification: that asks for a runtime-uniform Boone carrier and universal constants; this treats one fixed Fanizza instance, retains its native signal, and permits every constant and modulus to depend computably on that instance.
  fanizza-turing-bcs-signal-collapse: that starts from a near-perfect BCS strategy and collapses its native signal; this constructs that strategy from an arbitrary finite-dimensional approximate representation of one finitely presented group.
---

Fix a machine index `m` and its finite Fanizza BCS `B_m`.  There is an
effective finite group presentation `Gamma_m` containing the original BCS
involutions, including `d_m=x_(D,m)`, with these properties.

1. Every finite-dimensional unitary tuple of total squared relator energy
   `E` produces a commuting-operator strategy `S_E` for `B_m` and an exact
   Bob involution `X_(D,m)` such that

```text
epsilon(S_E)<=omega_m(E),
||U(d_m)-X_(D,m)||_2<=nu_m(E),                         (FPL1)
```

   where `omega_m(E),nu_m(E)` are computable and tend effectively to zero.
2. Every exact perfect marked representation of `B_m` becomes, after
   countable amplification, an exact representation of `Gamma_m` which
   retains the action of every original BCS word.

The construction uses only finitely many roles because the nonlinear Fanizza
menu and every truth table are fixed and finite.  For each oriented
rank-one occurrence, put its gauge-doubled packet in a free Thompson
occurrence orbit.  Split the rank-jump carrier into its equal-scale active and
exit atoms.  Route the complete four-atom endpoint table into a two-bit site
tag: its distinguished atom is the first-hit exit and its three-atom
complement is the survivor to be installed in the next occurrence.  Linear
BCS relations remain ordinary involution, commutator, and parity relators.

After fixed finite-group exactification, let `q_(r,n)` be the active mass and
`e_(r,n)` the first-hit exit mass for role `r` at level `n`.  Conditional on
the tagged-survivor incidence theorem, the oriented Fanizza branch identities
and two-bit tag prefix estimate give

```text
2q_(r,n)<=q_(r,n+1)+e_(r,n)+D_(r,n),
e_(r,n)<=q_(r,n)+Z_(r,n),
e_(r,n)>=eta_r q_(r,n)-H_(r,n),
sum_(n<N)e_(r,n)<=1,                                  (FPL2)
```

where `eta_r>0` is rational and, for computable constants and a polynomial
`p_r`,

```text
D_(r,n)+Z_(r,n)+H_(r,n)
 <= C_r p_r(n)sqrt(E).                                (FPL3)
```

Every base forbidden probability is bounded by a fixed sum of the
`q_(r,0)` plus the same exactification loss.  Consequently `(BFE6)` gives a
computable vanishing bound for every forbidden probability and hence
`(FPL1)`.

No uniformity in `m`, ambient matrix dimension, or machine runtime is used.
On the exact side, perfectness makes all forbidden exit atoms zero.  Gauge
covariance balances the private hard signs, free occurrence amalgams retain
contextuality, and countable amplification absorbs the finite packet and HNN
multiplicities.  Thus the original membership GNS representation, and in
particular a nontrivial `d_m`, survives.

This claim is intentionally conditional on
`tagged-s3-survivor-installs-next-recurrent-carrier`.  Merely returning the
three active atoms by HNN and charging a separate pulse does not imply the
prefix incidence in `(FPL2)`; the exact countermodel is
`free-occurrence-hnn-return-does-not-preserve-first-hit-prefix`.
