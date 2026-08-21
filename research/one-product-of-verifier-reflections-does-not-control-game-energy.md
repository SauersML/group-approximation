---
rg: 2
id: one-product-of-verifier-reflections-does-not-control-game-energy
kind: claim
title: One coherent product of verifier reflections can cancel while every tested state loses
distinct_from:
  fanizza-product-gram-reduces-to-one-state-holonomy: that identifies the one genuine cycle word whose state action must be charged; this rules out replacing the full Gram-Rayleigh row by an arbitrary sequential product of local verifier reflections.
  fanizza-heat-filter-has-uniform-cstar-decay: that uses a positive functional calculus of the complete game Hamiltonian; a product of reflections is unitary and has no comparable positivity.
---

Let `L_1,...,L_m` be rejected-event projections for a finite verifier and
put

```text
H_game=sum_j mu_j L_j,
R_j=I-2L_j.                                             (PVR1)
```

Each `R_j` is a reflection.  It is tempting to replace the positive
Gram-Rayleigh energy

```text
tr(G^*H_gameG)/||G||_2^2                               (PVR2)
```

by the fixed-vector defect of one coherent word

```text
W=R_m...R_1,
||(W-I)G||_2^2/||G||_2^2.                              (PVR3)
```

There is no such implication, even in dimension two and even at zero word
defect.  Take any nonzero projection `P` and two identical tests

```text
L_1=L_2=P.
```

Then

```text
R_2R_1=(I-2P)^2=I,                                    (PVR4)
```

so `(PVR3)` vanishes for every `G`, whereas on every nonzero `G` with
`PG=G`,

```text
tr(G^*H_gameG)/||G||_2^2=1.                            (PVR5)
```

Thus sequential coherent checks can cancel their phases exactly.  A fixed
product being close to identity is not evidence that its individual tests
accept.

This does not rule out a source-specific spectral theorem for a specially
designed Fanizza walk.  It does rule out deriving one merely from the fact
that the factors are verifier reflections.  A valid coherent verifier must
retain positivity, for example through a clocked `SELECT(R_j)`/acceptance
compression, a heat filter, or a direct finite Hecke moment whose Rayleigh
quotient dominates `(PVR2)`.  Constructing that controlled sum is exactly an
additional packet cell; it is not supplied by multiplying the existing
context HNN stable letters.

For the native Fanizza incidence, the product which is structurally forced
is instead the triangle holonomy `(FPG13)` in
`fanizza-product-gram-reduces-to-one-state-holonomy`.  Charging its action on
the same `G` is necessary for gluing the context gauges, but it still must be
combined with the positive local predicate and anchor rows in `(FPG19)`.
Holonomy fixedness alone cannot replace the game Hamiltonian.
