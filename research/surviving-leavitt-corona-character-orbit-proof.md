---
rg: 2
id: surviving-leavitt-corona-character-orbit-proof
kind: route
title: Exclude finite character orbits using the root-kernel finite-quotient argument
target: surviving-leavitt-corona-character-has-infinite-parabolic-orbit
requires:
  - steinberg-cover-fd-triviality
---

For `h in H`, conjugating `(PCO1)` shows that

```text
P_h=rho(h)P rho(h)^(-1)
```

is a global `N`-character projection for

```text
(h chi)(v)=chi(h^(-1) v h).                            (PCP1)
```

Two nonzero projections carrying distinct characters are orthogonal.  Choose
`v in N` on which the two signs differ.  The two projections are spectral
subprojections of the opposite eigenspaces of the same involution `rho(v)`.
Also one nonzero projection cannot carry two distinct characters.  Therefore
the projection orbit and the character orbit have the same cardinality.

Suppose this orbit is finite.  Permuting it gives a homomorphism

```text
H -> Sym(H chi).                                        (PCP2)
```

Composing with the permutation-matrix representation is a
finite-dimensional unitary representation of `St_(n-1)(L)`.  Since
`n-1>=3`, `steinberg-cover-fd-triviality` makes `(PCP2)` trivial.  Thus
`h chi=chi` for every `h in H`.

Write a character of `N=(L,+)^(n-1)` as

```text
chi(v_1,...,v_(n-1))=product_i chi_i(v_i).              (PCP3)
```

For distinct `i,j<n`, conjugation by `x_ij(r)` performs the elementary
column shear

```text
(v_i,v_j) |-> (v_i+r v_j,v_j)                           (PCP4)
```

up to the immaterial characteristic-two convention.  Apply invariance to a
column with `v_j=1` and all other entries zero.  Equations `(PCP3)--(PCP4)`
give

```text
chi_i(r)=1                         for every r in L.     (PCP5)
```

For every `i` there is a distinct `j`, so all `chi_i` are trivial.  Hence
`chi` is trivial, contrary to the hypothesis.  The orbit is infinite.
