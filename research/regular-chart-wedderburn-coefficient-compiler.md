---
rg: 2
id: regular-chart-wedderburn-coefficient-compiler
kind: claim
title: Regular finite-group chart words compile canonically to finite multiplicity-corner path sums
---

Let `G` be a fixed finite group, let `lambda` be its left regular
representation, and let

```text
H_k = l2(G) tensor C^k.
```

There is a finite family of elements of the complex group algebra, depending
only on `G`, which canonically exposes all external multiplicity coordinates
of every operator `X in B(H_k)` and turns products of ambient operators into
finite path sums of coefficient products, with constants independent of `k`.

More precisely, for each irreducible representation `sigma` of degree
`d_sigma`, choose Fourier matrix units

```text
e^sigma_ab in C[G]
```

for the corresponding Wedderburn block and put `p_sigma=e^sigma_11`.  In
`lambda tensor I_k`, the corner `p_sigma H_k` has dimension `d_sigma k`.
For every ambient operator `X` define its coefficient blocks

```text
X^(sigma,tau)_(a,c)
  = e^sigma_(1,a) X e^tau_(c,1)
  : p_tau H_k -> p_sigma H_k.
```

Then `X` is recovered exactly from this finite block family, adjoints are
blockwise adjoints with source and target exchanged, and multiplication is
the exact finite path-sum rule

```text
(XY)^(sigma,upsilon)_(a,e)
 = sum_(tau,c) X^(sigma,tau)_(a,c) Y^(tau,upsilon)_(c,e).
```

Consequently every fixed noncommutative word or polynomial in operators on a
regular `G`-multiple has a canonical finite coefficient program over fixed
matrix amplifications of the external multiplicity algebra.  Compression,
reconstruction and any fixed finite path sum have normalized-Hilbert--Schmidt
bounds whose constants depend only on `G` and the fixed program, never on
`k`.

For the atlas application `G=A_8`, this gives a basis-free finite Fourier IR
for the single unknown relative chart unitary in
`leavitt-regular-atlas-hyperlinearity-criterion`.  It does **not** assert that
atlas relators already force a Leavitt coefficient algebra; it only removes
coordinate access and multiplicity bookkeeping as separate obstacles.  The
remaining problem is to find a finite compiled coefficient identity with a
matrix-only obstruction.