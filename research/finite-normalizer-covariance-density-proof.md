---
rg: 2
id: finite-normalizer-covariance-density-proof
kind: route
title: Restrict regular semidirect quotients to the old and packet factors
target: finite-normalizer-covariance-density-no-go
requires:
  - property-t-laplacian-sos-certificate
---

Start with any finite-index normal subgroup `N` of `Gamma`.  If `C` acts on
`Gamma`, then

```text
N_C=intersection_(c in C) c(N)
```

is finite-index, normal and `C`-invariant.  Moreover `Gamma/N_C` surjects
onto `Gamma/N`, so applying this operation to an unbounded quotient tower
keeps its orders unbounded.

Write `F=Q semidirect C`.  The left cosets of `Q` in `F` give an orthogonal
decomposition

```text
ell^2(F)=directSum_(c in C) ell^2(Q)c.                         (1)
```

On the `c`-summand the left action of `Q` is its regular action precomposed
with the automorphism induced by `c`.  Relabelling the basis of `Q` makes
all `|C|` summands equal to `lambda_Q`.  The commutant of `lambda_Q` has
dimension `|Q|`; the commutant of `|C| lambda_Q` is

```text
M_|C|(C) tensor C[Q]^op,
```

of dimension `|C|^2|Q|`.  Since `dim ell^2(F)=|C||Q|`, division by the
square of the Hilbert dimension proves `(FAC2)`.

The property-`(T)` Laplacian has a uniform positive lower bound on the
orthogonal complement of invariant vectors in every unitary
representation.  Applied to the adjoint representation on `End(ell^2(F))`,
any fixed cutoff below that bound therefore selects exactly
`End_Gamma(ell^2(F))`.

Likewise, the left cosets of `C` show that

```text
lambda_F restricted to C = |Q| lambda_C.                       (2)
```

Functional calculus in the fixed finite group algebra then gives `(FAC3)`.
On adjoint spaces, `(2)` identifies

```text
End(ell^2(F))=End(ell^2(C)) tensor M_|Q|(C)
```

as an `A`- and `B`-module.  Therefore

```text
R_A-R_B=(R_A^C-R_B^C) tensor I_(M_|Q|),
```

whose rank is `rank(R_A^C-R_B^C)|Q|^2`.  Dividing by
`|F|^2=|C|^2|Q|^2` proves `(FAC4)`.  All covariance relations are exact
because the representation factors through the genuine semidirect quotient
`F`.

For the reverse action `theta:Gamma->Aut(B)`, the diagonal image `Q'` in
`Q times theta(Gamma)` projects onto `Q`, so `|Q'|>=|Q|`, and `theta`
factors through `Q'`.  Therefore `B semidirect Q'` is a finite quotient of
`B semidirect Gamma`.  Repeating the same coset calculation with the normal
packet subgroup and the old complement gives

```text
lambda_(B semidirect Q') restricted to Q' = |B| lambda_(Q'),
lambda_(B semidirect Q') restricted to B  = |Q'| lambda_B.
```

The old commutant density is again `1/|Q'|`, while every packet projection
mass and packet Reynolds density is independent of `Q'`.  This proves the
second normalizer direction.
