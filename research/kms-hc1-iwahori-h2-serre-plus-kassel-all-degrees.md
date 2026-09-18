---
rg: 2
id: kms-hc1-iwahori-h2-serre-plus-kassel-all-degrees
kind: claim
title: In every degree and for every p>=5 the pro-p Iwahori Lie algebra has only the six Serre relations and one Kassel relation at each 3mp; integrally H_2 = Serre + HC_1 away from 6, and p-images of class <= 3p-1 kill w_p for all p>=5
distinct_from:
  kms-hc1-iwahori-integral-h2-serre-plus-hc1: that claim computes H_2(L_Z) exactly through degree 90 and reduces Open 1 to a torsion statement, without proving it in any degree beyond the computation. This claim proves that torsion statement, and Open 1, in all degrees by an explicit cocycle argument, and gives the tower bound 3p-1 for every p>=5 (that claim has min(3p-1, 90)).
  kms-hc1-a2-iwahori-towers-deviate-only-at-kassel-degrees: that claim proves the deviation bound (B) and the lower bound (K), and leaves Open statements 1 and 2. This claim resolves Open statement 1; Open statement 2 is untouched.
artifacts:
  - experiments/kms-hc1-iwahori-h2-all-degrees-2026-09-18/cocycle_check.py
  - experiments/kms-hc1-iwahori-h2-all-degrees-2026-09-18/cocycle90.out
  - experiments/kms-hc1-iwahori-laplacian-2026-09-17/lap.py
  - experiments/kms-hc1-iwahori-laplacian-2026-09-17/linkage.py
  - experiments/kms-hc1-iwahori-laplacian-2026-09-17/h2z120.out
---

Notation of `kms-hc1-iwahori-integral-h2-serre-plus-hc1`.

- `L_Z` is the Chevalley `Z`-form of the pro-p Iwahori Lie algebra, and
  `L_p = L_Z (x) F_p = gr_P(I_1)`.
- `D_p = {k : H_2(L_p)_k != 0}`.
- A weight is `mu = nu + m delta`, where `nu` is in the finite root lattice of
  `A_2` and `m = c_0`.
- `Q(nu) = (nu,nu)/2` and `c(mu) = deg(mu) - Q(nu)`.

**(A1) All minimal relations, all degrees, every p >= 5.** For every prime
`p >= 5` and every weight `mu`:

```text
dim H_2(L_p)_mu = 1   if mu is one of the six Serre weights of degree 3 (rho - w rho, l(w) = 2),
                  1   if mu = n delta with p | n,
                  0   otherwise.
```

Hence `D_p = {3} + 3pN`, with `dim H_2(L_p)_3 = 6` and `dim H_2(L_p)_{3mp} = 1`.
This is Open statement 1 of
`kms-hc1-a2-iwahori-towers-deviate-only-at-kassel-degrees`, now proved.

The proof works with the dual, the 2-cocycles of weight `-mu` on `L_p`. For
`m >= 4` it splits by the type of `nu`. By the root-system count
`Q(nu)` is in `{0,1,3,4}`, and each type is settled by triples of one shape.

- `nu = 0`: triples with one Cartan factor force the cocycle to be affine in
  the loop exponent, with one common slope `B` and `n B = 0`. The triples of
  three root vectors leave exactly the coboundaries plus `B`.
- `Q = 4` and `Q = 3`: triples with one Cartan factor force the cocycle to
  be 0. For `Q = 4` this needs `p` odd. For `Q = 3` it needs `p != 3`; this
  is where the `(Z/3)^6` family comes from.
- `nu` a root: triples with one Cartan factor gauge away the Cartan part and
  kill the root-vector part. Two families of triples of root vectors then
  kill the one boundary term.

For `m <= 3` every weight of `Lambda^2 L` has degree `<= 13`. Those weights
are covered by the exact table (Z2) of the integral claim, which here is
recomputed through degree 120 (`h2z120.out`: 282 weights, 0 anomalies).

The lower bound 1 at `n delta` is the Kassel cocycle (K). The machine check
`cocycle_check.py 90 5 7 11 13 17 19` restricts the cocycle conditions to
exactly the triple shapes used in the proof. It confirms that they already
cut `H^2` down to the stated value at every weight with `m >= 4` and degree
`<= 90`: 3042 (weight, p) pairs, 0 differ.

**(A2) Integral form: Serre plus `HC_1` of the Iwahori order, away from 6.**
In all degrees,

```text
H_2(L_Z) (x) Z[1/6] = Z[1/6]^6 (degree 3)  +  sum_{n >= 2} Z[1/6]/n   (weight n delta, degree 3n).
```

The proof combines three facts:

- By (A1) and the universal coefficient theorem, `Tors H_2(L_Z)` has, for
  each `p >= 5`, one invariant factor divisible by `p` at `n delta` with
  `p | n`, and none elsewhere.
- The integral Kassel cocycle `a tr(XY) [a+b = n]` has order exactly `n` in
  `H^2(L_Z; Z/n)`, so `H_2(L_Z)_{n delta}` maps onto `Z/n`.
- Kostant's Laplacian (A4) kills `H_2(L_Z)_{n delta} (x) Z[1/3]` by
  `c = 3n`.

So the `p`-part is exactly `Z/p^{v_p(n)}`. The free part is `Z^6` in
degree 3, since every other weight has `H_2(L_p) = 0` for some `p >= 5`.
This is the sharper form conjectured in (Z6) of the integral claim, the
Kassel--Loday statement `H_2 = Serre + HC_1(Lambda)` for the Iwahori order
`Lambda`, with 6 inverted.

**(A3) Towers for every p >= 5.** By (A1), the degree-3 agreement (Z5) and
the deviation bound (B), for every prime `p >= 5`,

```text
|Gamma^A2_p / P_k| = |I_1 / P_k|   for all k <= 3p.
```

So every p-group image of `Gamma^A2_p` of p-class `<= 3p - 1` factors
through `I_1` and kills `w_p`. Before, (Z5) of the integral claim gave this
only for `k <= min(3p, 91)`. So for `p >= 31`, where it gave p-class
`<= 90`, the bound now grows linearly in `p`.

**(A4) Laplacian, all homological degrees.**

- On `Lambda^j(L_Z)_mu (x) Z[1/3]`,
  `d d* + d* d = c(mu) Id`. Here `d*` is the adjoint for the contravariant
  form (root vectors orthonormal, Cartan block the Cartan matrix, Gram
  determinants powers of 3).
- So `c(mu)` kills `H_j(L_Z)_mu (x) Z[1/3]` for every `j`, and
  `H_*(L_p)_mu = 0` unless `p | c(mu)`, for every `p != 3`.
- This is the identity of Kostant (finite type) and Garland--Lepowsky
  (Kac--Moody). `lap.py` checks it exactly for `j = 1,2` through degree 36:
  300 blocks, 0 failures.
- `linkage.py check h2z120.out` confirms that every prime `!= 3` in the
  torsion of the degree-120 table divides `c(mu)`: 282 weights, 0
  violations.

**(A5) The criterion now rests on Open statement 2 alone.** By (A1) and (B),
for each `p >= 5`, `phi^: Gamma^A2_p -> I_1` is an isomorphism iff, at each
Kassel class `3mp`, the single Kassel direction dies in `Gamma^`. That
means `dim gr_{3mp}(Gamma^) = dim gr_{3mp}(I_1)`, given agreement below it.
No other class can deviate. So `r(I_1) <= 9` and the regularity gate of
`kms-hc1-a2-pro-p-completion-is-iwahori-criterion` are equivalent to Open 2
for every `p >= 5`. Open 2 is known in the computed cases:

| p | Kassel degrees decided |
| --- | --- |
| 5 | 15, 30, 45 |
| 7 | 21, 42 |
| 11 | 33 |

Scope. (A1) is a proof: the hand cocycle argument for `m >= 4`, and the exact
integral table for the finitely many weights with `m <= 3`. (A2), (A3) and
(A5) are proofs given (A1), (A4), (B), (K) and (Z5). (A4) is a cited
published identity, re-derived in the route and certified by exact check
through degree 36. It is used only in (A2), for the exponent. Not claimed:

- Open statement 2 (the Kassel directions die at group level);
- the 2- and 3-parts of `H_2(L_Z)`.

Proof: `kms-hc1-iwahori-h2-serre-plus-kassel-all-degrees-proof`.
