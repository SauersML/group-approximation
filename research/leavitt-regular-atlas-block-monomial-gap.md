---
rg: 2
id: leavitt-regular-atlas-block-monomial-gap
kind: claim
title: Block-monomial and bounded-complexity transports cannot close the regular Leavitt atlas
distinct_from:
  leavitt-regular-atlas-permutation-cover-impossible: that rules out scalar monomial permutations through the all-central-cover theorem; this gives an explicit gap even with arbitrary unitary fibre rotations and a trace-weighted escape law for every bounded internal matrix size.
  block-monomial-coordinate-collapse: that concerns coordinate models of the Kun--Thom wreath crossed product; this concerns the two regular A8 charts in the finite Leavitt atlas.
  atlas-stabilizer-commutant-no-go: that excludes a different ansatz `U=DJ` by an exactly forced surviving relation and assumes no block-monomial structure.
artifacts:
  - notes/EXPLICIT_LEAVITT_ATLAS.md
---

Write `n=|A_8|=20160` and decompose the atlas space as
`ell^2(A_8) tensor C^k`. Let

```text
F_k(U)=max_(s in bar S) ||pi_U(s)-1||_2.
```

For the block-monomial subgroup

```text
W_k = U(k) wr Sym(A_8) <= U(nk),
```

one has the uniform explicit bound

```text
F_k(U) >= 1/sqrt(5040)             (U in W_k).          (BMG1)
```

Moreover `F_k` is uniformly word-Lipschitz in `U`. Thus every sequence with
`F_k(U_k)->0` remains a fixed normalized-HS distance from `W_k`.

There is a stronger internal-complexity fence. If the `n by n` block
coefficients of `U` generate

```text
D(U) = direct_sum_j (M_(r_j)(C) tensor I_(ell_j)),
```

and

```text
w_R(U)=sum_(r_j<=R) r_j ell_j/k,
```

then for every fixed `R` there is `e_R>0`, independent of `k`, such that

```text
F_k(U)^2 >= e_R w_R(U).                                  (BMG2)
```

Consequently every successful atlas sequence must have asymptotically all
Hilbert-space weight escape every bounded internal matrix size. In
particular, rational permutation absorbers, arbitrary fibre rotations,
commutative mixtures, and uniformly subhomogeneous internal algebras cannot
be glued into a positive witness. The smallest live positive target is a
delocalized relative unitary with genuinely growing noncommutative internal
dimension; generic Haar/asymptotically-free mixing is separately known to
land at defect `sqrt(2)`, so the witness must occupy a structured intermediate
regime.

This escape is quantitatively nonclassical. If `c(U)` is the maximum
normalized-HS commutator norm among the real and imaginary parts of the block
coefficients of `U`, then there is `c_0>0`, independent of `k`, such that every
certificate sequence satisfies

```text
liminf_k c(U_k) >= c_0.                                  (BMG3)
```

Thus even asymptotically commuting operator-valued transport is excluded.
