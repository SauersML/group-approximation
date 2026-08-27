---
rg: 2
id: atlas-finite-nontrivial-s3-shell-pays-boundary
kind: claim
title: Finite regular frames with fixed nontrivial S3 mass pay a five-boundary defect floor
refuted_by: atlas-group-microstate-collapse-is-subgroup-containment
distinct_from:
  atlas-six-relator-regular-face-defect-floor: that asks for a floor on the five boundary defects plus collision centrality over every regular frame; this deletes the collision word and restricts to one explicit positive-mass shell in the two nontrivial collision channels.
  atlas-19243-forces-sign-or-standard-channel-mass: that uses collision to put mass in the sign or standard channel; this asks the five boundary words alone to separate the aggregate nontrivial-channel shell from zero in finite matrices.
  atlas-six-relator-factor-retains-half-nontrivial-s3-mass: that gives an exact finite-factor countermodel to universal boundary charging; this is deliberately finite-dimensional and therefore isolates the required category boundary.
  atlas-typed-hard-interior-comb-row-census: that asks for an authenticated extension-labelled incidence carrying five operator paths; this asks only for one scalar boundary floor and never selects an S4 extension coordinate.
---

**REFUTED.**  The proposed target was the following.  Let
`K=<h_a,h_b>~=S3` be the collision subgroup and decompose a
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

This would have been a sufficient strictly smaller row target for
`atlas-six-relator-regular-face-defect-floor`: collision centrality does not
occur in `(NSB2)`, no bridge or additive row occurs, and only the fixed
closed shell `(NSB3)` is tested.  The reduction with the exact threshold
`1/1024` is given in
`atlas-collision-shell-boundary-floor-reduction`.

It is false even with the matrix qualifier.  The finite characteristic-two
affine model in
`atlas-group-microstate-collapse-is-subgroup-containment` has

```text
E=M semidirect A8,   dim_F2(M)=155,
```

and its left regular representation restricts to exactly regular copies of
both marked `A8` charts.  Every one of the 234 first-boundary words vanishes,
so in particular

```text
B_5(U)=0.                                              (NSB4)
```

The same exact computation gives the two raw `S3` covariance energy

```text
e(U)=a(U)^2+b(U)^2=4.                                  (NSB5)
```

The established `S3` channel diagonalization gives

```text
e(U)<=8m_epsilon(U)+6m_sigma(U)<=8m_nt(U),
```

and therefore

```text
m_nt(U)>=1/2.                                          (NSB6)
```

This single finite regular frame violates `(NSB3)` by a factor far beyond
the proposed threshold `1/1024`.  It invalidates
`atlas-collision-shell-boundary-floor-reduction`.

The canonical exact Leavitt factor independently has all five boundary words
zero and
`atlas-six-relator-factor-retains-half-nontrivial-s3-mass` gives the same
lower bound

```text
m_nt(U)>=1/2.                                          (NSB7)
```

Thus the failure is not merely a finite-factor category firewall: the
boundary-only channel-shell reduction is already dead in finite matrices.

## Consequence for the six-row floor

Writing `E_K` for the `K`-Reynolds projection still gives

```text
m_nt(U)=||U-E_K(U)||_2^2.                              (NSB8)
```

but collision centrality cannot be used only to prove a lower bound for
`m_nt` and then be discarded.  The affine point has abundant nontrivial
channel mass and zero boundary energy; what excludes it from the six-row
face is precisely its macroscopic `c_19243` defect.  Any surviving analytic
proof must therefore retain a genuinely joint boundary--collision statistic,
not just the aggregate sign-plus-standard mass supplied by collision.

## Attempts

- The five-word derivative gap is local and does not exclude the affine
  component `(NSB4)--(NSB6)`.
- Passing from small collision defect to aggregate nontrivial-channel mass
  loses the information which distinguishes that affine component.
- A sign/standard split by itself does not repair the loss: the countermodel
  has positive aggregate mass, and a useful refinement must couple its
  channel source to the interior word rather than merely count it.
