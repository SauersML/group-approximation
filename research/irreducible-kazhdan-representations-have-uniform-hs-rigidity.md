---
rg: 2
id: irreducible-kazhdan-representations-have-uniform-hs-rigidity
kind: claim
title: Every irreducible Kazhdan representation has a uniform HS rigidity basin
artifacts:
  - research/artifacts/irreducible-kazhdan-local-hs-rigidity-2026-09-05.md
distinct_from:
  kazhdan-approximate-coefficients-have-curved-hodge-control: that retains supplied coefficient mass while improving its energy; this uses an irreducible same-dimensional comparison to turn the retained mass into a full unitary correction.
  kazhdan-irreducible-compressions-have-quadratic-defect: that starts from a rectangular compression and detects missing dimensions by Schur variance; this starts in the original irreducible dimension and obtains a same-dimensional correction in its conjugacy class.
---

Let G=<S|R> be a fixed finitely presented Kazhdan group, with the
inverse-label consistency conventions of the curved Hodge theorem.
There are eta0,L>0, independent of dimension, such that for every
irreducible rho:G->U(d) and every inverse-compatible tuple U,

```text
max_s||U_s-rho(s)||_(2,d)<=eta0
```

implies, for some unitary V in U(d),

```text
max_s||U_s-V* rho(s)V||_(2,d)<=L delta(U),
delta(U)=max_(r in R)||U(r)-I||_(2,d).                 (IHR1)
```

This is a full same-dimensional correction within the conjugacy class
of the supplied irreducible representation. It uses neither H2
vanishing nor a finite-image assumption. The basin radius is measured
in normalized HS norm; no operator-norm closeness is assumed. At zero
defect, the input is exactly unitarily equivalent to rho.

For symmetric S, the coarse-closeness assumption can instead be
replaced by one vector at a fixed coefficient spectral cutoff: there
is epsilon_*>0, independent of d and rho, such that

```text
min Spec Delta_(rho,U)<=epsilon_*^2,
Delta_(rho,U)=(1/h)sum_s D_s*D_s,
D_s(A)=rho(s)A-AU_s,
```

implies the same full linear correction `(IHR1)`. No positive spectral
count or operator-norm bound on the eigenvector is needed. Indeed,
when `a=2h epsilon^2/kappa^2<1`, a vector at eigenvalue at most epsilon^2
gives distance to the conjugacy class at most
`sqrt(h)epsilon+2sqrt(a/(1-a))`. Conversely orbit distance e gives
minimum eigenvalue at most e^2.

There is also a rectangular version. If a supplied irreducible
rho:G->U(N) has N>=d and its rectangular coefficient connection for U
has minimum eigenvalue at most epsilon_*^2, then some sigma conjugate
to rho satisfies

```text
max_s||sigma(s)-(U_s direct_sum I_(N-d))||_(2,N)
 <=L delta(U)sqrt(d/N),
(N-d)/d<=L^2 delta(U)^2/kappa^2,
min Spec Delta_(rho,U)<=L^2 delta(U)^2.                (IHR2)
```

Thus one fixed-cutoff vector into an irreducible target of at least
the input dimension gives a full linear flexible correction with
quadratic padding. In particular zero defect forces N=d. No
finite-image hypothesis is required for either version.

The original dimension is required for the no-padding conclusion.
In all versions the supplied comparison must be irreducible. The
theorem does not provide such a comparison or a spectral vector for
arbitrary tuples, does not apply to a reducible comparison obtained
by dilution, and does not claim that the conjugating unitary is close
to the identity at the rate delta(U).

DERIVATION
contractive-heat-schur-scalar-and-polar-rigidity-proof
