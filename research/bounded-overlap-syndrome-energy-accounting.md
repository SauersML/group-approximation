---
rg: 2
id: bounded-overlap-syndrome-energy-accounting
kind: claim
title: Local syndrome charges with bounded overlap sum to a global Hilbert-Schmidt energy bound
distinct_from:
  extensive-cosystolic-index-defect: that asks for a presentation which produces the local syndromes; this is only the finite combinatorial accounting lemma once local charges have been supplied
---

Let `J` index local syndrome carriers with nonnegative normalized masses
`q_j`, and let a finite set `R` index nonnegative relator energies `e_r`.
Suppose there are neighborhoods `N(j) subset R` and constants `L,D>0` such
that

```text
q_j <= L * sum_(r in N(j)) e_r                       (local charge)
```

for every `j`, and every relator `r` belongs to at most `D` of the
neighborhoods `N(j)`.  Then

```text
sum_j q_j <= L D * sum_(r in R) e_r.                  (BOE)
```

Consequently any dimension-independent lower bound `sum_j q_j>=beta>0`
forces a dimension-independent global energy floor

```text
sum_r e_r >= beta/(L D).
```

This is the exact finite incidence-counting step needed after a qLDPC or
cosystolic construction has localized a marked spectral carrier.
