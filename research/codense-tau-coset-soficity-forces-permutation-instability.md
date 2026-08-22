---
rg: 2
id: codense-tau-coset-soficity-forces-permutation-instability
kind: claim
title: A sofic coset action for a co-dense tau pair forces a noncorrectable permutation approximation
distinct_from:
  codense-kazhdan-coset-action-forces-permutation-outliers: that assumes the subgroup itself is Kazhdan and gives a finite-atlas gap; this uses only the uniform gap on the exact finite A-actions, so it applies to PSL2(Z) inside PSL2(Z[1/2])
  hnn-over-sl2-z-not-sofic-if-sl2-z-inverse-p-p-stable: that applies the same co-density and expansion to the stable-letter graph inside a hypothetical sofic approximation of an HNN extension; this extracts the obstruction directly from orbit charts for A acting on A/C
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that is a normalized-Hilbert--Schmidt/Connes-embedding implication; this is a Hamming/permutation theorem
artifacts:
  - research/artifacts/psl2-bruhat-tits-soficity-fork-2026-08-21.md
---

Let `C<A` be a proper finitely generated subgroup.  Assume that there is a
finite generating set `S_C` and `kappa>0` such that, for every finite action
`rho:A->Sym(V)`, the restriction to `C` on `l2(V)` has spectral gap at least
`kappa` relative to its invariant vectors.  Assume also that

```text
rho(C)=rho(A)                                                     (CTS1)
```

for every finite action `rho` of `A`.

If the transitive action `A action A/C` is sofic, its witnessing
approximately multiplicative permutation maps are not flexibly correctable
to genuine finite actions of `A`.  In particular,

```text
A flexibly permutation-stable  ==>  A action A/C is not sofic.    (CTS2)
```

The statement allows the usual flexible padding by a vanishing proportion
of points.  The proof is quantitative: after transferring an orbit atlas of
error `epsilon` to an exact action at Hamming distance `eta`, the contradiction
has the form

```text
1-O(epsilon+eta) <= O((epsilon+eta)/kappa^2).                      (CTS3)
```

Thus it is not merely the failure of finite quotients to separate `C`; every
sofic model of the coset action must live in the noncorrectable sector.

