---
rg: 2
id: stw82-commutative-max-formula-with-maximal-cutdown-overlap
kind: claim
title: A commutative maximum-formula extension has unavoidable maximal two-cut overlap
---

Consider the endpoint-evaluation extension

```text
0 -> C_0((0,1)) -> C([0,1]) -> C directSum C -> 0.    (E1)
```

Every positive contractive approximate unit `(h_lambda)` of `C_0((0,1))`
is quasicentral in `C([0,1])` and eventually satisfies

```text
norm(h_lambda(1-h_lambda))=1/4.                       (E2)
```

Nevertheless (E1) obeys the nuclear-dimension maximum formula:

```text
dim_nuc(C([0,1]))
 = 1
 = max(dim_nuc(C_0((0,1))),dim_nuc(C directSum C)).   (E3)
```

In particular, a direct sum of maps whose unit supports are the
complementary raw cuts `h_lambda` and `1-h_lambda` has a fixed cross-product
defect at those units, even in a positive case of STW Problem LXXXII.
Therefore a general one-colour proof cannot consist solely of perturbing
those two raw supports; it must reorganize the endpoint approximations or
absorb the transition region by some additional mechanism.
