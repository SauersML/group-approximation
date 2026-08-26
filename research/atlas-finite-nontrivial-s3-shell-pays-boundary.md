---
rg: 2
id: atlas-finite-nontrivial-s3-shell-pays-boundary
kind: claim
title: Finite regular frames with fixed nontrivial S3 mass pay a five-boundary defect floor
distinct_from:
  atlas-six-relator-regular-face-defect-floor: that asks for a floor on the five boundary defects plus collision centrality over every regular frame; this deletes the collision word and restricts to one explicit positive-mass shell in the two nontrivial collision channels.
  atlas-19243-forces-sign-or-standard-channel-mass: that uses collision to put mass in the sign or standard channel; this asks the five boundary words alone to separate the aggregate nontrivial-channel shell from zero in finite matrices.
  atlas-six-relator-factor-retains-half-nontrivial-s3-mass: that gives an exact finite-factor countermodel to universal boundary charging; this is deliberately finite-dimensional and therefore isolates the required category boundary.
  atlas-typed-hard-interior-comb-row-census: that asks for an authenticated extension-labelled incidence carrying five operator paths; this asks only for one scalar boundary floor and never selects an S4 extension coordinate.
---

**OPEN.**  Let `K=<h_a,h_b>~=S3` be the collision subgroup and decompose a
regular common-frame unitary under diagonal `K`-conjugation as

```text
U=U_1+U_epsilon+U_sigma,
m_nt(U)=||U_epsilon||_2^2+||U_sigma||_2^2.             (NSB1)
```

For the five saturated boundary words put

```text
B_5(U)=sum_(j in {0,11,30,44,55})
                    ||pi_U(s_j)-1||_2^2.              (NSB2)
```

Prove that there is a constant `beta_5>0`, independent of the external
regular multiplicity, such that

```text
m_nt(U)>=1/1024  ==>  B_5(U)>=beta_5                 (NSB3)
```

for every `U in U(20160k)` and every `k>=1`.

This is a sufficient strictly smaller row target for
`atlas-six-relator-regular-face-defect-floor`: collision centrality does not
occur in `(NSB2)`, no bridge or additive row occurs, and only the fixed
closed shell `(NSB3)` is tested.  The reduction with the exact threshold
`1/1024` is given in
`atlas-collision-shell-boundary-floor-reduction`.

The matrix qualifier is essential.  In the canonical exact Leavitt factor,
all five boundary words vanish while
`atlas-six-relator-factor-retains-half-nontrivial-s3-mass` gives

```text
m_nt(U)>=1/2.                                         (NSB4)
```

Thus `(NSB3)` is false for arbitrary finite tracial von Neumann algebras.
It cannot follow from a universal tracial sum of squares, an identity in the
six-relator quotient, or Murray--von Neumann dimension inequalities alone.
External amplification preserves both sides, so fixed congruence, parity,
and bounded rank-rounding arguments are also unavailable by
`atlas-fixed-rank-arithmetic-cannot-authenticate-s3-incidence`.

## Exact remaining finite-coordinate problem

Write `E_K` for the `K`-Reynolds projection.  Then

```text
m_nt(U)=||U-E_K(U)||_2^2.                              (NSB5)
```

Consequently `(NSB3)` is a scalar separation problem for the five explicit
boundary word maps on a fixed spectral shell of one fixed finite-group
action.  It does not require the extension-labelled `S4` census.  A valid
proof must nevertheless use a dimension-activated matricial feature: the
same shell contains the exact Leavitt factor point `(NSB4)`, while tensor
amplification removes every bounded integral residue.  Concretely, the
remaining admissible mechanisms are a dimension-dependent singular-space
loss for the five boundary maps or an equivalent positive-density matrix
rank obstruction.

## Attempts

- The five-word derivative form has a uniform gap off the `H` commutant, but
  the characteristic-two affine boundary model and the exact factor point
  show that this local gap does not globalize by ordinary compactness.
- Charging `m_nt` by a fixed tracial polynomial in the boundary words is
  impossible by `(NSB4)`.
- Splitting `(NSB3)` into sign and standard estimates is unnecessary for the
  scalar six-row floor; collision centrality forces their aggregate mass.
- Fixed-rank arithmetic cannot supply `beta_5`, because amplification leaves
  `m_nt` and normalized boundary energy unchanged.
