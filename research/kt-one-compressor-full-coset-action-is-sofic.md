---
rg: 2
id: kt-one-compressor-full-coset-action-is-sofic
kind: claim
title: One Kun--Thom compressor acts soficly on the entire ambient coset set
distinct_from:
  monomial-ascending-hnn-coset-action-sofic: that treats the distinguished orbit H/Gamma; this treats the restriction of H to every orbit in the ambient set G/Gamma, whose stabilizers include arbitrary Laurent elementary conjugates
  kun-thom-single-compressor-sofic-joint-nonsofic: that localizes the canonical obstruction on the two distinguished one-compressor orbits; this proves soficity on the whole ambient coset set needed by the finitary-factor normalizer problem
  positive-core-bernoulli-ce: that treats the Gamma-action on the positive semigroup of sites; this includes the stable letter and all ambient sites
---

Use the regular finite-field Kun--Thom data

```text
R_0=k[N^d],       R=k[Z^d],
Gamma=EL_r(R_0),  E=EL_r(R),  G=E rtimes SL_d(Z),
X=G/Gamma.
```

Let `A in SL_d(Z) intersect M_d(N)` be a proper monomial compressor and put
`H_A=<Gamma,A>`.  Then the restriction

```text
H_A action X
```

is sofic.  Hence the doubled action on `Y=X x {0,1}` is sofic as well.

The new point beyond the distinguished orbit is a uniform stabilizer
separation lemma.  Write the telescope kernel as

```text
N_A=union_(j>=0) Gamma_j,     Gamma_j=A^(-j) Gamma A^j.
```

For every ambient site `gGamma` and every `j`, the stabilizer

```text
Gamma_j intersect g Gamma g^(-1)
```

is separable in `Gamma_j`.  The proof uses only a finite polynomial-ring
truncation: after writing `g=eL`, a matrix outside the stabilizer has, after
conjugation by `e`, a nonzero Laurent coefficient outside the monoid ring
`k[L N^d]`; a sufficiently deep truncation of the polynomial ring
`k[A^(-j)N^d]` preserves that coefficient despite the fixed finite Laurent
support of `e` and `e^(-1)`.

Orbitwise soficity at every telescope level, increasing-union permanence,
and cyclic-extension permanence then give the claim.

DERIVATION
kt-one-compressor-full-coset-action-proof
