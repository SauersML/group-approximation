---
rg: 2
id: thompson-free-occurrence-amalgam-preserves-contextuality
kind: claim
title: A Thompson-indexed free occurrence amalgam is finitely presented and adds no cross-occurrence commutation
distinct_from:
  thompson-clifford-central-product-tape: that uses a restricted direct sum, so different sites commute; this uses a free product over the common mark precisely to keep different context occurrences noncommuting.
  finite-orbit-occurrence-pauli-compiler: that must also prove robust decoding for an unbounded test family; this is the exact finite-presentation theorem for copies of one fixed finitely presented occurrence group.
  context-local-schur-packet-marked-extension: that extends the finitely many contexts of one BCS occurrence on a Hilbert space; this places countably many freely independent occurrences on a Thompson orbit.
---

Let `H=<S_H|R_H>` be finitely presented with a named central involution `J`,
and let Thompson `V` act transitively on its rational-tail orbit `X`.  Form

```text
F_X(H)=(*_(<J>,x in X) H_x) semidirect V,              (TFO1)
```

where the copies are freely amalgamated only over their common `J`, `V`
permutes them, and no other relations are imposed between distinct sites.
Then `F_X(H)` is finitely presented.

Indeed, choose a base site `x_0`, finite presentations for `H` and `V`, and a
finite generating set `T` for the point stabilizer `V_(x_0)`.  A presentation
is obtained from those generators and relators by adding

```text
[t,s]=1             (t in T, s in S_H),
[v,J]=1             (v in a finite generating set of V).           (TFO2)
```

The first family makes the copy of `H` independent of the transporter naming
its site; the second identifies the central signs of all conjugate copies.
There are deliberately no off-diagonal commutator relators.

The common `J` survives whenever it survives in `H`: send `V` to the identity
and fold every `H_x` onto the same copy of `H`.  This gives a retraction
`F_X(H)->H` preserving `J`.

Consequently a complete gauge-doubled Fanizza context/packet occurrence may
be placed at every Thompson site while retaining all sharing relations inside
one occurrence and imposing no commutation between logical variables in
different occurrences.  Every word of `H_x` is fixed by the point stabilizer
of `x`.
