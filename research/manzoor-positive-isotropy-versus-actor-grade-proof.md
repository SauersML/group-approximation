---
rg: 2
id: manzoor-positive-isotropy-versus-actor-grade-proof
kind: route
title: Compare a positive IRS fixed-word trace with the zero trace of a nonidentity actor grade
target: manzoor-irs-generators-cannot-be-single-actor-grade
requires:
  - manzoor-isotropy-has-no-positive-finite-type-corner
  - centralizer-aperiodic-haar-actor-marginals-force-regular-trace
---

The Manzoor stabilizer `S` is infinite almost surely, in particular
`mu(S!={e})=1`. Since `F` is countable,

```text
{S:S!={e}} = union_(w in F, w!=e) {S:w in S}.
```

Therefore there is some `w!=e` with

```text
chi_mu(w)=mu({S:w in S})>0.                            (MHP1)
```

Assume `(MHA1)`--`(MHA2)`. The actor grading of the crossed product is
multiplicative. Applying `(MHA2)` along the reduced word for `w` gives

```text
Psi(pi_mu(w)) = B_w U_(theta(w))                       (MHP2)
```

for some `B_w in U(L(A))`; inverses cause no problem because the inverse of a
homogeneous unitary is homogeneous in the inverse grade. Injectivity of
`theta` and `w!=e` give `theta(w)!=e`. The canonical conditional expectation
onto `L(A)` kills every nonidentity actor grade, so

```text
tau(B_w U_(theta(w)))=0.                               (MHP3)
```

On the other hand trace preservation and the IRS GNS definition give

```text
tau(Psi(pi_mu(w)))=tau_(P_mu)(pi_mu(w))=chi_mu(w)>0,   (MHP4)
```

contradicting `(MHP3)`. The trace-completion lemma is what permits `(MHP3)`
to be inferred already inside an abstract exact covariant packet from its
Haar lamp and regular actor marginals.
---
