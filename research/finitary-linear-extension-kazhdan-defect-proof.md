---
rg: 2
id: finitary-linear-extension-kazhdan-defect-proof
kind: route
title: Two nilpotent matrix units produce a central involution in the defect of a subgroup
target: finitary-linear-extension-kazhdan-defect-kills-kernel
requires:
  - normal-kazhdan-defect-non-mf
artifacts:
  - research/artifacts/finitary-linear-vs-permutation-kazhdan-criterion-2026-09-08.md
---

Notation as in `(FL1)` and `(FL2)`; `T_(pq) = I + E_(pq)` for distinct
`p,q in Y`, and all matrices are over `F_2`, so `T_(pq)^2 = I`.

## 1. The configuration

Put

```text
c = T_(xb),      y = T_(a,ux),      z = T_(ab),      H = <L, u, c, y> <= G.
```

`L` fixes `x` by `(FL2)` and fixes `b` because `b` is `V`-fixed, so conjugation
by `L` fixes the matrix unit `E_(xb)`, i.e.

```text
c in C_H(L).
```

Conjugation by `u` carries `E_(xb)` to `E_(ux,b)`, again because `b` is fixed,
so `u c u^-1 = T_(ux,b)`.

## 2. The defect element

With `ell in L` from `(FL2)`,

```text
d = [u c u^-1, ell] = T_(ux,b) T_(ell u x, b)^-1.
```

The two row indices `ux` and `ell u x` are distinct, which is precisely the
third hypothesis of `(FL2)`; the column index `b` is common. Because the two
matrix units share a column and have distinct rows, their product vanishes and

```text
d = I + E_(ux,b) + E_(ell u x, b).
```

`d` is a compression defect of the configuration `(L, u, c)` in `H`: `L` is
Kazhdan, `u` compresses `L` into itself by `(FL2)`, and `c` centralizes `L`.
So `d in D_H(L)`, and `D_H(L)` is normal in `H`.

## 3. The central involution

Set `A = E_(a,ux)` and `B = E_(ux,b) + E_(ell u x, b)`, so `y = I + A` and
`d = I + B`.  Then

```text
A^2 = 0,   B^2 = 0,   B A = 0,   A B = E_(ab),
```

the first three because the relevant row and column indices disagree (`a` is
not `ux`, the columns of `B` are `b` while its rows are `ux` and `ell u x`,
and `a != ux, ell u x`), and the fourth because only the `E_(ux,b)` summand of
`B` composes with `A`.  All longer products vanish.  Hence

```text
[y, d] = (I+A)(I+B)(I+A)(I+B) = I + AB = I + E_(ab) = z,
```

using characteristic two for the inverses.  Normality of `D_H(L)` in `H` gives
`z in D_H(L)`.

`z` commutes with `L` and with `u` because `a` and `b` are fixed by `V`, and
with `c` and `y` because `E_(ab)` shares no index in the required position
with `E_(xb)` or `E_(a,ux)` -- explicitly, `E_(ab)E_(xb) = E_(xb)E_(ab) = 0`
and `E_(ab)E_(a,ux) = E_(a,ux)E_(ab) = 0`.  So `z` is central in `H`, and
`z^2 = I`, so

```text
<z> = C_2 <= Z(H) cap D_H(L).
```

## 4. Applying the criterion inside `H`

A finite group has property (T): if every group element displaces a unit
vector by less than one, averaging over the group produces a nonzero invariant
vector.  So `<z>` is a nontrivial normal property-(T) subgroup of `H` lying in
`D_H(L)`, and the prerequisite applies **to `H`**: every homomorphism from `H`
to an MF group kills `z`.

If `phi : G -> M` with `M` MF, its restriction to `H` is such a homomorphism,
so `phi(z) = 1`.

## 5. From one transvection to the whole kernel

`ker phi` is normal in `G`, so it contains the normal closure of `z`.
Conjugating `z = T_(ab)` by the finitary permutation matrices of `K` carries it
to `T_(pq)` for every ordered pair of distinct `p, q in Y`.  These transvections
generate `K`: Gaussian elimination over `F_2` reduces an invertible finitary
matrix to the identity using row additions and row swaps, and over `F_2` a swap
is a product of three row additions.  Hence `K <= ker phi`.

## 6. The radical

`K <= Rad_MF(G)` is the previous step quantified over `phi`.  If `V` is MF,
the quotient map `G ->> G/K = V` is a homomorphism to an MF group with kernel
exactly `K`, so `Rad_MF(G) <= K` and `(FL3)` follows.

Since `z != I`, no homomorphism from `G` to an MF group is injective, so `G` is
not MF.
