---
rg: 2
id: untwisted-bilateral-symbol-enrichment-is-lef
kind: claim
title: The untwisted bilateral Jacobson symbol enrichment is LEF
artifacts:
  - research/periodic-laurent-reduction-preserves-finite-action-table.md
distinct_from:
  binary-jacobson-monomial-symbol-preimage-is-marked-mf: that handles the actual one-sided preimage of the monomial symbol subgroup; this treats every Laurent elementary symbol but only in the untwisted bilateral semidirect product.
  binary-jacobson-core-is-weakly-sofic-with-fd-head-radical: that records the weak-sofic status of the actual Toeplitz extension; this proves LEF for a comparison group in which the extension cocycle has been removed.
  toeplitz-folner-compressions-cannot-retain-jacobson-head: that audits one-sided finite sections and finds equal boundary and head errors; bilateral periodic reduction has no boundary and therefore preserves finitary marks.
---

**ESTABLISHED.** Put

```text
A=F_2[z,z^(-1)],
V=A^n with basis X=Z x {1,...,n},
L=GL_fin(X,F_2),
Q=EL_n(A).
```

Here `GL_fin` means invertible linear maps whose matrix differs from
the identity in only finitely many entries. Laurent matrices in `Q`
and their inverses have finite propagation on `X`, so conjugation
defines an action

```text
alpha:Q -> Aut(L).
```

For every finite `n>=3`, the untwisted semidirect product

```text
H_bi=L semidirect_alpha Q                              (UBL1)
```

is LEF. In particular it is sofic and hyperlinear, and its finite local
models retain every prescribed nonidentity finitary transvection.

The local models are explicit. For sufficiently large `N`, reduce

```text
A -> A_N=F_2[z,z^(-1)]/(z^N-1)
```

and fold the finitely inspected matrix coordinates from `Z` into
`Z/NZ`. This gives a local embedding into the finite semidirect
product

```text
GL_(nN)(F_2) semidirect EL_n(A_N).                     (UBL2)
```

All selected Laurent products, finitary products and covariance rows
are exact once `N` exceeds the propagation and support diameters.

This gives a sharp firewall for the Jacobson candidate. The abstract
ingredients

```text
finitary GL kernel + Laurent elementary quotient + linear covariance
```

are compatible with head-retaining finite local models when assembled
without a Toeplitz twist. Therefore a construction or obstruction for

```text
EL_n(F_2<S,T | TS=1>)
```

must control the actual one-sided extension cocycle. Replacing it by
the bilateral semidirect product erases the load-bearing relation.

Alekseev--Bradford, arXiv:2601.18742, gives a general 2026
sofic-action/halo permanence framework for related semidirect products.
The proof here is self-contained and covers the present finite
propagation action directly; it does not claim that the actual
Toeplitz extension splits.

DERIVATION
periodic-laurent-reduction-preserves-finite-action-table
