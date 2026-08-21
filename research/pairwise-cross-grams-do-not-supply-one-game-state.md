---
rg: 2
id: pairwise-cross-grams-do-not-supply-one-game-state
kind: claim
title: Positive pairwise cross-Grams do not supply one state good for all contexts
distinct_from:
  one-gram-vector-decodes-a-finite-bcs-strategy: that proves one common Gram operator with low total game energy is sufficient; this gives an exact finite-dimensional countermodel when a different Gram state is used for every pair.
  localized-non-ce-leakage-forces-cross-gram-overlap: that extracts one positive pairwise overlap from capacity and localized leakage; this shows that the selected pairwise overlap need not decode the full static game.
  consistency-defect-is-state-dependent-distance: that identifies consistency and distance when they are measured in one state; this shows that consistency measured in different edge states cannot be glued by that identity.
---

Pairwise positive overlap, even with exact pairwise consistency on the
overlap, does not imply the existence of the single Gram vector required by
`one-gram-vector-decodes-a-finite-bcs-strategy`.

Let the context set have `k>=3` elements and put

```text
H=directSum_({c,d} subset {1,...,k}) H_(cd),            (PGS1)
```

with every `H_(cd)` nonzero and of the same dimension.  Define

```text
Q_c=sum_(d!=c)1_(H_(cd)).                               (PGS2)
```

Then the `Q_c` commute and

```text
tau(Q_c)=2/k,
tau(Q_cQ_d)=1/binom(k,2)>0                 (c!=d),
sum_c Q_c=2I.                                           (PGS3)
```

Thus every pair has a positive exact cross-Gram carrier

```text
G_(cd)=1_(H_(cd)),                                     (PGS4)
```

and arbitrary occurrence measurements for contexts `c,d` can be made
identical and perfect on that carrier.  Different edges may therefore have
zero state-dependent consistency defect in their own states.

Nevertheless, for every density matrix `rho` on `H`,

```text
(1/k)sum_c tr(rho Q_c)=2/k.                            (PGS5)
```

If the local predicate for context `c` is guaranteed only on `Q_c`, the
uniform average probability of being in a certified context carrier is at
most `2/k`.  For `k=4`, as in the native Fanizza incidence, this is exactly
`1/2`, despite **every** pairwise cross-Gram moment being positive.  There is
no common nonzero intersection:

```text
meet_c Q_c=0.                                          (PGS6)
```

This is an exact finite-dimensional model, not an asymptotic dilution.  It
persists under arbitrary common amplification.

The obstruction is that each edge uses a different state `vec(G_(cd))`.
State-dependent triangle inequalities compare measurements only inside one
fixed state.  They cannot concatenate the zero defects of `(PGS4)` around a
cycle or across a leaf when the Gram vector changes at every edge.

Consequently the positive overlap selected by `(NCL6)` is insufficient by
itself to decode the fixed static game.  A valid state-dependent bypass must
produce one operator `G` for which the **sum over all contexts** in `(OGV3)`
is small.  The minimal additional mixed moment is therefore not another
pairwise overlap scalar.  It is the single game-Laplacian Rayleigh quotient

```text
E_G/||G||_2^2,                                         (PGS7)
```

equivalently the finite moment list `(OGV12)` evaluated on the same `G`.

Canonical trace does not repair this countermodel.  It is exactly the state
used in `(PGS3)--(PGS5)`.  Canonical-trace occurrence consistency **does**
decode a strategy when all defects are global, corresponding to `G=I` in
`(OGV3)`.  What fails is replacing that one global state by separately
normalized context or edge carriers.
