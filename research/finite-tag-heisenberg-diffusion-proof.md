---
rg: 2
id: finite-tag-heisenberg-diffusion-proof
kind: route
title: Tensor the finite Stone--von Neumann models and count polarized atoms
target: finite-tags-do-not-atomize-heisenberg-schrodinger-tower
requires: []
---

Realize the Schrödinger representation on the standard basis
`{delta_x:x in F_p^N}` by

```text
pi_N(X(v)) delta_x=zeta^(<v,x>) delta_x,
pi_N(Y(w)) delta_x=delta_(x+w),
pi_N(Z)=zeta I.
```

For `M>=N`, write

```text
F_p^M=F_p^N directSum F_p^(M-N),
K_M=K_N tensor K_(M-N).
```

The first-coordinate copy of `H_N` acts as `pi_N tensor I`, proving
`(FTH1)`.  Since the central character is `zeta` throughout, the marked
central projection is the identity.  Restriction multiplicities are exactly
`p^(M-N)`, so the normalized multiplicity densities obey the ordinary
branching identities without error.

For `chi in dual(F_p^N)`, Fourier orthogonality gives

```text
e_chi=p^(-N) sum_v conjugate(chi(v)) pi_M(X(v)).
```

This is the projection onto one value of the first `N` coordinates.  It has
rank `p^(M-N)`, proving `(FTH2)`.  After tensoring with a fixed packet of
dimension `D`, a joint projection `e_chi tensor f_j` has normalized trace

```text
p^(-N) rank(f_j)/D <= p^(-N).
```

Orthogonality and trace additivity give `(FTH3)` for a union of at most `C`
such atoms.  The same calculation says that `L` atoms have trace at most
`L p^(-N)`, so trace at least `alpha` forces `L>=alpha p^N`, proving
`(FTH4)`.  All statements are exact finite-dimensional identities; no
limit, stability theorem, or asymptotic estimate is used.

Finally `(FTH1)` identifies the commutant of the restricted irreducible
Heisenberg action as

```text
I_(p^N) tensor M_(p^(M-N))(C).
```

Its unitary group is `(FTH5)`.  Tensoring by `sigma` does not remove the
subgroup obtained by placing the identity on the packet factor.  Conjugating
an inter-window identification by this subgroup preserves the entire finite
group table, every central weight, and every fixed packet moment while
changing its multiplicity-space placement arbitrarily.
