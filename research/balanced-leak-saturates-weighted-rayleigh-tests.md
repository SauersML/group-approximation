---
rg: 2
id: balanced-leak-saturates-weighted-rayleigh-tests
kind: claim
title: A balanced arithmetic leak saturates every weighted one-vector Rayleigh test
distinct_from:
  lambda-exact-face-closes-at-p-three: that node's weighted no-go optimizes Schur-intertwiner support over exact finite-representation isotypic measures and obtains the sharp square-root total-variation modulus; this is an exact scalar coefficient identity in an arbitrary tracial model, with no exactness, type decomposition, or scale profile.
  single-hecke-average-isometry-for-lambda-central-unitaries: that open claim asks for the Hilbert--Schmidt NORM of one explicit lazy Hecke average to equal one in matrix ultraproducts; this proves only its one-vector Rayleigh coefficient for arbitrary weights and explicitly leaves the cross-Gram norm of the averaged translates uncontrolled.
  full-arithmetic-bernoulli-projection-orbit-is-free-spherical: that computes every joint moment of the coset-Bernoulli orbit and makes all distinct coset vectors orthogonal; this needs only one balanced projection and its first h-overlap, so it also applies to a homogeneous-quotient leak with that moment without asserting a Bernoulli orbit.
  homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse: that constructs nonconstant Lambda-invariant K-orbit indicators and proves some arithmetic generator moves them; this audits the stronger balanced-quarter moment, when present, against all scalar weighted double-coset averages.
---

Let `Lambda<G` be groups, let `pi:G->U(M)` be a unitary representation in a
finite tracial von Neumann algebra `(M,tau)`, and let `h in G`.  Suppose that
`q in M` is a projection satisfying

```text
[q,pi(lambda)]=0              (lambda in Lambda),
tau(q)=1/2,
tau(q pi(h) q pi(h)^*)=1/4.                              (BLR1)
```

For every finitely supported probability weight `omega` on the double coset
`Lambda h Lambda`, define the conjugation average

```text
H_omega(z)=sum_g omega(g) pi(g) z pi(g)^*.
```

Then

```text
tau(q H_omega(q))=1/4.                                  (BLR2)
```

Equivalently, for the centered unit vector `x=2q-I` in `L^2(M,tau)`,

```text
<x,H_omega(x)>=0,
sum_g omega(g)||pi(g)xpi(g)^*-x||_2^2=2.                (BLR3)
```

Thus changing the positive weights cannot improve any one-vector
Kazhdan/Hecke Rayleigh comparison: every weighted target average has the same
zero coefficient against the `Lambda`-fixed vector `x`, while every weighted
source average supported in `Lambda` fixes `x` exactly.  More generally the
lazy average

```text
S_(t,omega)=t Id+(1-t)H_omega
```

has the forced Rayleigh quotient `<x,S_(t,omega)x>=t` for every choice of
`omega`.

The conclusion does **not** determine `||H_omega(x)||_2`.  That norm contains
the cross-Gram coefficients between distinct double-coset translates, which
are absent from the single-vector Rayleigh data.  Consequently this is a
firewall against optimizing scalar Kazhdan weights, not a refutation of a
multi-translate norm, matrix-coordinate, or cocycle argument.

For the homogeneous-quotient crossed product of
`homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse`, `(BLR2)`
applies whenever the finite `K`-orbit algebra contains a `Lambda`-invariant
union `q` with the balanced moment `(BLR1)`.  The statement is conditional on
that balanced cut; it does not assert that every cocompact lattice quotient
has one.

## Attempts

- **Why the weighted-TV theorem does not subsume this.**  The estimate
  `(P3F7)--(P3F10)` in `lambda-exact-face-closes-at-p-three` starts from two
  exact congruence representations and their irreducible multiplicity
  measures.  Here the identities hold before exactification and remain valid
  on the homogeneous crossed-product enemy, where no finite-level isotypic
  profile is available.  Conversely `(BLR2)` is only one scalar coefficient
  and says nothing about the total-variation overlap of type measures.
- **Unrun lightweight MSI experiment.**  At small congruence levels
  `SL_3(Z/p^a)`, form the finite Gram matrix of the double-coset translates
  of a candidate balanced projection and minimize
  `omega^* G omega` over the probability simplex.  This convex quadratic
  optimization measures `||H_omega(x)||_2^2`, precisely the cross-Gram datum
  not fixed by `(BLR2)`.  It is recorded only as a future one-core sparse MSI
  screen; it has not been run, supplies no numerical evidence, and no Cairn
  route depends on it.

