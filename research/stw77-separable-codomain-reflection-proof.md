---
rg: 2
id: stw77-separable-codomain-reflection-proof
kind: route
title: Retain countably many nuclear approximations and proper-infiniteness witnesses
target: stw77-counterexamples-reflect-to-separable-codomains
requires: []
artifacts:
  - research/artifacts/stw77-map-oinfty-audit-2026-08-30.md
---

Put `C=phi(A)` and `d=dim_nuc(phi)`.  Choose increasing finite subsets with
dense union in the unit ball of `A`.  For the `n`th set choose a
`(d+1)`-color nuclear-dimension approximation to `phi` within `1/n`.
Adjoin to `C` the ranges of all outgoing finite-dimensional maps in these
countably many approximations.  This retains witnesses proving

```text
dim_nuc(phi:A->B_0) <= d.                              (1)
```

Because `phi` is not O-infinity-stable, the central-isometry defect
criterion supplies a finite subset `F` of `A` with

```text
kappa_phi(F)>0.
```

Every pair of isometries in `B_0` is also a pair of isometries in `B`, so
the infimum defining the defect can only increase when the codomain is
shrunk:

```text
kappa_(phi_0)(F) >= kappa_phi(F)>0.                    (1a)
```

It remains to retain pointwise proper infiniteness using only countably many
elements.  Choose a norm-dense sequence `(c_j)` in the positive unit ball of
`C`.  For every `j` and positive rational `q` for which

```text
h_(j,q)=(c_j-q)_+
```

is nonzero, proper infiniteness in `B` gives

```text
h_(j,q) directSum h_(j,q) <=_Cu h_(j,q).              (2)
```

Choose one sequence of Cuntz implementers for each relation (2), and adjoin
all their matrix entries.  Let `B_0` be the unital C-star algebra generated
by `C`, the approximation ranges, and these countably many implementers.
It is separable, and (1)--(2) hold inside `B_0`.

We verify that every `0!=a in C_+` is properly infinite in `B_0`.  Fix
`0<epsilon<||a||` and choose `c_j` with

```text
||a-c_j|| < eta < epsilon/3.
```

Choose a positive rational `q` with

```text
eta < q < epsilon-eta.
```

The standard perturbation comparison for positive elements gives

```text
(a-epsilon)_+ <=_Cu (c_j-q)_+ <=_Cu a.                (3)
```

The middle element is nonzero whenever the left one is, and (2)--(3) yield

```text
2[(a-epsilon)_+] <= 2[(c_j-q)_+]
                   <= [(c_j-q)_+] <= [a].             (4)
```

Taking the supremum over `epsilon` in the Cuntz semigroup gives
`2[a]<=[a]`; hence `a` is properly infinite in `B_0`.

Finally, (1a) directly shows that `phi_0` is not O-infinity-stable.
Equivalently, a unital copy of `O_infinity` in
`(B_0)_omega intersect phi(A)'` would remain such a copy after applying the
injective sequence-algebra map induced by `B_0 subset B`, making `phi`
O-infinity-stable.  Thus failure reflects quantitatively to `B_0`.

No literature theorem beyond standard Cuntz perturbation and cutdown facts
is used.
