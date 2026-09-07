---
rg: 2
id: double-swap-involution-normal-generation-proof
kind: route
title: Decompose the double transposition into three signed swaps and take two commutators
target: double-swap-involution-normally-generates-elementary-group
requires:
  - universal-seed-group-collapses-elementary-groups
artifacts:
  - research/artifacts/involution-normal-generator-2026-09-07.md
---

## Proof

### `sigma` is elementary

The 2x2 block of `w_ij = e_ij(1) e_ji(-1) e_ij(1)` on coordinates `(i,j)` is
`[[0,1],[-1,0]]`, so on basis vectors

```text
w_12 : e_1 |-> -e_2, e_2 |-> e_1,   fixing e_3, e_4
w_34 : e_3 |-> -e_4, e_4 |-> e_3,   fixing e_1, e_2
w_13^2 = diag(-1, 1, -1, 1),         minus the identity on the (1,3) plane
```

Applying `w_13^2`, then `w_34`, then `w_12`:

```text
e_1 |-> -e_1 |-> -e_1 |-> e_2
e_2 |->  e_2 |->  e_2 |-> e_1
e_3 |-> -e_3 |->  e_4 |-> e_4
e_4 |->  e_4 |->  e_3 |-> e_3
```

which is `sigma`.  So `sigma = w_12 w_34 w_13^2 in EL_m(R)`.  It is a
nonidentity permutation matrix over a nonzero ring, and permutation matrices
compose as permutations, so `sigma^2 = 1` and the order is exactly two.

### `sigma` normally generates

Conjugation by a permutation matrix moves indices, `sigma e_ij(r) sigma^(-1)
= e_(sigma(i) sigma(j))(r)`, so with `[a,b] = a b a^(-1) b^(-1)`

```text
[e_13(r), sigma] = e_13(r) . sigma e_13(-r) sigma^(-1) = e_13(r) e_24(-r),
```

the two factors commuting because `2 != 3` and `4 != 1`.  Next, `e_12(1)`
commutes with `e_13(r)`, since `E_12E_13 = E_13E_12 = 0`, and the Steinberg
relation gives `[e_12(1), e_24(-r)] = e_14(-r)`, so
`e_12(1) e_24(-r) e_12(-1) = e_14(-r) e_24(-r)`.  Therefore

```text
[e_12(1), e_13(r)e_24(-r)]
  = e_13(r) e_14(-r) e_24(-r) . e_24(r) e_13(-r)
  = e_13(r) e_14(-r) e_13(-r)
  = e_14(-r),
```

the last step because `e_13` and `e_14` commute (`E_13E_14 = E_14E_13 = 0`).
Unwinding both commutators writes `e_14(-r)` as a product of four conjugates
of `sigma`, the conjugators being `e_13(r)`, `e_12(1)` and their products.
Conjugating further by the `w_ij` carries `(1,4)` to any `(i,j)` with
`i != j`, up to a sign absorbed by letting `r` range over `R`, and those roots
generate `EL_m(R)`.

Every coefficient appearing is `+-1` or the arbitrary `r`, so no
characteristic hypothesis and no invertibility of `2` is used.

### Transfer to the seed group

`universal-seed-group-collapses-elementary-groups` supplies, for each nonzero
countable unital ring `R` with a properly infinite unit and each `n >= 2`, a
homomorphism `f : B = EL_4(C) --> EL_n(R)` whose image normally generates the
target.  Apply the calculation above inside `B` at `m = 4`: the normal closure
of `sigma` is all of `B`, so the normal closure of `f(sigma)` contains
`f(B)`, whose normal closure is `EL_n(R)`.  If `EL_n(R) != 1` then
`f(sigma) != 1`, and `f(sigma)^2 = 1`, so `f(sigma)` is an involution.
