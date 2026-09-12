---
rg: 2
id: three-depth-one-leavitt-return-enumeration
kind: route
title: Collapse pair products, filter by one row-column cross, and test the full signed normalizer
target: three-depth-one-leavitt-roots-never-return
requires:
  - two-depth-one-leavitt-roots-return-only-constantly
artifacts:
  - experiments/depth_one_triple_leavitt_return_search.py
---

# Exact enumeration of three depth-one returns

## 1. Faithful coefficient normal form

As in the established two-factor search, represent the binary Leavitt
monomial `s_mu t_nu` by the prefix replacement

```text
nu gamma |-> mu gamma.
```

The identity

```text
(mu,nu)=(mu0,nu0)+(mu1,nu1)
```

moves every finite sum to a common domain depth.  Cancellation is in
characteristic two, and prefix cancellation multiplies monomials.  This is a
faithful normal form for the finite sums occurring in the search; equality is
therefore exact.

The script first reruns the two-factor regression.  It recovers `304`
individually nonnormal roots and exactly `338` normalizing ordered pairs, all
of which have constant products, matching
`two-depth-one-leavitt-roots-return-only-constantly`.  This pins the root
orientation, multiplication convention, signed character, and normalizer
membership test before the new enumeration starts.

## 2. Exact reduction from triples to pair products

For roots `x,y,z`, whether `xyz` normalizes `(L_0,lambda_0)` depends only on
the exact matrix product `xy` and on `z`.  Among the `304^2` ordered first-two
factor choices there are exactly

```text
54,897
```

distinct matrices in prefix normal form.  Keeping one representative of each
therefore represents every one of the

```text
304^3=28,094,464
```

ordered triples without identifying two products which act differently.

## 3. The row-column support filter is logically exact

Let `r=x_ab(c)` be the proposed third root and let `H` be the conjugate of one
constant Hecke generator by the first-two-factor product.  Since `r` is an
involution in characteristic two,

```text
r H r
```

is obtained by one elementary row operation on row `a` and one elementary
column operation on column `b`.  Every entry outside

```text
(row a) union (column b)
```

is unchanged.  Hence, if any such entry of `H` is nonconstant in the faithful
prefix normal form, `rHr` cannot be a constant matrix and the candidate cannot
normalize `L_0`.  Rejecting it at this stage is therefore a theorem, not a
heuristic signature or finite evaluation.

## 4. Full signed-normalizer verification

Every candidate surviving the support filter is conjugated exactly against
the ten generators of `L_0`.  For each generator the checker requires:

1. every coefficient entry is exactly `0` or `1`;
2. the resulting binary matrix lies in the complete `8,192`-element ledger of
   `L_0`; and
3. its value under `lambda_0` equals the prescribed sign of the original
   generator.

Using generator order

```text
2,3,5,0,7,8,9,1,6,4
```

only for early rejection, the aggregate survivor counts are

```text
4,181,384
2,335,930
1,099,624
253,920
23,736
23,736
6,130
0
0
0.
```

No candidate survives the eighth row.  Thus no triple normalizes the signed
pair, proving (DTR8).

The executable contains all counts as assertions.  Any change to the prefix
algebra, the signed finite group, the root menu, the support filter, or the
verdict makes the checker fail rather than silently changing the claim.

No Property `(T)`, Kazhdan input, trace profile, numerical tolerance, random
sampling, or external classification theorem enters this calculation.
