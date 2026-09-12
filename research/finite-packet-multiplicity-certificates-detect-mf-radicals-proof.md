---
rg: 2
id: finite-packet-multiplicity-certificates-detect-mf-radicals-proof
kind: route
title: Exactify each finite packet and apply the rational dimension alternative
target: finite-packet-multiplicity-certificates-detect-mf-radicals
requires:
  - finite-corona-dimension-certificate-calculus
  - finite-root-heisenberg-multiplicity-germs
---

The restriction of `rho` to a finite subgroup extends to a unital
star-homomorphism from its finite-dimensional group C-star algebra into
`Q_d`.  Exactify the finitely many packet algebras simultaneously on one
cofinite coordinate tail.  At coordinate `n`, ordinary finite-group
representation theory gives

```text
rho_n|_(F_a) ~= directSum_(pi in Irr(F_a)) C^(m_(a,pi,n)) tensor pi.
                                                               (FPP1)
```

The sequence `[m_(a,pi,n)]` is the multiplicity germ `mu_(a,pi)`.

If `F_a<=F_b`, restricting `(FPP1)` for `F_b` and decomposing each
irreducible gives

```text
m_(a,sigma,n)=sum_pi Res_(sigma,pi) m_(b,pi,n).          (FPP2)
```

Conjugacy by `g` gives a unitary equivalence between the corresponding
coordinate packet representations up to a norm-null error.  Averaging over
the finite group and polar-correcting the resulting intertwiner makes this
equivalence exact on a cofinite tail, so the paired multiplicities agree.
Refinement and spectral-cut relations follow from the same finite-dimensional
decomposition.  Hence all chosen constraints hold as literal integer
equalities `B m_n=0` eventually.

Pairing `(FPM1)` with a nonnegative multiplicity vector `m_n` gives

```text
-m_(a,pi,n)=s.m_n>=0.
```

Thus the selected multiplicity is zero eventually, proving `(FPM2)`.

If every irreducible type on which `z` acts nontrivially has zero
multiplicity, the remaining coordinate representation of `F_a` sends `z` to
the identity.  Therefore `rho(z)=1` in the corona, proving `(FPM3)`.  Normal
generation gives the full-radical conclusion.

Completeness for the stated finite constraints is the converse part of
`finite-corona-dimension-certificate-calculus`: absence of `(FPM1)` yields a
rational nonnegative solution with positive selected coordinate, and clearing
denominators produces an exact integer multiplicity assignment.  The root
and Heisenberg specialization is supplied by
`finite-root-heisenberg-multiplicity-germs`.
