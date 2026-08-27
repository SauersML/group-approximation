---
rg: 2
id: low-dimensional-hyperoctahedral-packet-proof
kind: route
title: Classify the low-degree odd bipartitions of the hyperoctahedral group
target: low-dimensional-hyperoctahedral-packet-groupifies-any-predicate
requires: []
artifacts:
  - experiments/hyperoctahedral_low_degree_packet.py
  - experiments/hyperoctahedral-low-degree-packet.json
---

The irreducible representations of `W_m=C_2 wr S_m` are indexed by
bipartitions `(lambda,mu)` with `|lambda|+|mu|=m`.  Their dimensions and
central signs are

```text
dim(lambda,mu)=binom(m,|mu|) f^lambda f^mu,
pi_(lambda,mu)(J)=(-1)^|mu| I.                          (1)
```

Thus the marked irreducibles have `|mu|` odd.  For even `m>=8`, if
`3<=|mu|<=m-3`, then

```text
dim(lambda,mu)>=binom(m,3)>=m(m-2).                    (2)
```

If `|mu|=1`, equation `(1)` gives `m f^lambda`.  Apart from the trivial and
sign representations of `S_(m-1)`, every Specht degree is at least `m-2`.
The same argument applies to `|mu|=m-1`.  Therefore the only marked
irreducibles below `m(m-2)` have dimension `m`: the two one-dimensional
Specht choices over weight one and the two over weight `m-1`.

On restriction to the diagonal `(C_2)^m`, the weight-one modules contain
the `m` coordinate characters.  The weight-`m-1` modules contain their
complements.  For every selector `x`, even repetition gives

```text
product_(j=1)^m d_x(j)
  =product_(a in R) a_x^L=1.                            (3)
```

Hence a complementary diagonal character evaluates on every `d_x` exactly
as its omitted coordinate character.  Both weight-one and weight-`m-1`
modules therefore have the same joint selector spectrum: the chosen labelled
multiset of allowed assignments.  This proves `(HLP3)` and the direct-sum
statement.
