---
rg: 2
id: packet-natural-selector-no-go-proof
kind: route
title: Apply Schur's lemma twice, first to the packet and then to its multiplicity unitaries
target: packet-natural-selectors-cannot-extract-one-bounded-copy
requires: []
---

Because `P_m` reduces `pi_m(K)`, Schur's lemma gives

```text
P_m=I_r tensor Q_m
```

for a projection `Q_m in M_m`.  Equation `(PNS1)` now says

```text
WQ_mW^*=Q_m                 for every W in U(m).
```

The commutant of `U(m)` consists only of scalars, so `Q_m` is a scalar
projection and hence is `0` or `I_m`.  This proves `(PNS2)`.

For a fixed packet/normalizer representation `sigma` on `C^r`, restrict to
one irreducible summand and apply the same argument to
`sigma tensor I_m`.  Common amplification always restores the full
multiplicity automorphism group, regardless of how many finite packet words
or finite automorphisms the rule uses.  Only data acting nontrivially on the
multiplicity space can evade the conclusion.
