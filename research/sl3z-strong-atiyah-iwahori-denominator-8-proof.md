---
rg: 2
id: sl3z-strong-atiyah-iwahori-denominator-8-proof
kind: route
title: Restrict K_I to Gamma(3) and Gamma(4), induce from K_I to SL_3(Z), and compare gcds
target: sl3z-strong-atiyah-iff-discrete-iwahori-denominator-8
requires:
  - p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah
---

Let `G = SL_3(Z)`, `Gamma(m) = ker(G -> SL_3(Z/m))`, and `K_I` as in the claim.

**Two rank formulas.**
- **Restriction.** For `H <= G` of finite index and `A` over `C[G]`,
  `rk_G(A) = rk_H(res A) / [G:H]`, as in `sl3z-atiyah-denominators-48-proof`.
- **Induction.** For any subgroup `H <= G` and `B` over `C[H]`,
  `rk_G(B) = rk_H(B)`. Right multiplication by `C[H]` preserves each `l^2(tH)`,
  so `l^2(G)^n` is the orthogonal sum over left cosets `tH` of translates of
  `l^2(H)^n`, and the kernel projection of `B` is diagonal. The trace
  `sum_i <P (delta_e (x) e_i), delta_e (x) e_i>` reads only the summand
  `l^2(H)^n`.

**Strong Atiyah inputs.** `Gamma(3) <= CS(1,3,3)` and `Gamma(4) <= CS(2,3,2)`,
which are torsion-free compact `p`-adic analytic groups. So by
[[p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah]] every subgroup of
`Gamma(3)` or of `Gamma(4)` has integer ranks.

**Item 1.**
- `G -> SL_3(F_2)` is onto, `|SL_3(F_2)| = 168` and `|U| = 8`, so
  `[G : K_I] = 21`.
- By Minkowski's bound every finite subgroup of `GL_3(Q)` has order dividing
  `48 = 2^4 * 3`. If `F <= G` is a 2-group then `F x {+-I} <= GL_3(Z)` has order
  `2|F|`, so `|F|` divides 8.
- `K_I` has no element of order 3. Such an element maps to 1 in the 2-group
  `U`, so it lies in `Gamma(2)`. Since `(I + 2X)^2 = I + 4(X + X^2)`, its square
  lies in `Gamma(4)`, which is torsion-free. So finite subgroups of `K_I` are
  2-groups of order dividing 8.
- `D_8 = <r, s>` with `r = [[0,-1,0],[1,0,0],[0,0,1]]` and `s = diag(1,-1,-1)` is
  dihedral of order 8, since `srs = r^(-1)`. Its image mod 2 is a 2-group, so
  it lies in a conjugate of `U`. Lifting the conjugating element to `G` puts a
  conjugate of `D_8` inside `K_I`.

**Item 2.** Let `B` be a matrix over `C[K_I]`.
- `L = K_I cap Gamma(3)` has integer ranks. `K_I` contains `Gamma(2)`, and
  `Gamma(2)` maps onto `SL_3(Z/3)`, because `G -> SL_3(Z/6) = SL_3(Z/2) x SL_3(Z/3)`
  is onto. So `[K_I : L] = 5616` and `rk_{K_I}(B) in (1/5616)Z`.
- `Gamma(4) <= Gamma(2) <= K_I`, with index `43008 / 21 = 2048 = 2^11`, using
  `[G : Gamma(4)] = 43008`. So `rk_{K_I}(B) in (1/2048)Z`.
- `5616 = 2^4 * 351`, so `gcd(5616, 2048) = 16` and `rk_{K_I}(B) in (1/16)Z`.

**Item 3, first bullet implies second.** By induction,
`rk_{K_I}(B) = rk_G(B) in (1/24)Z`. With item 2,
`rk_{K_I}(B) in (1/24)Z cap (1/16)Z = (1/8)Z`.

**Item 3, second bullet implies first.** Restriction to `K_I` gives
`rk_G(A) = rk_{K_I}(res A) / 21 in (1/168)Z`. Restriction to `Gamma(3)` gives
`rk_G(A) in (1/5616)Z`. And `gcd(168, 5616) = 2^3 * 3 = 24`.

This is Linnell--Schick's Sylow reduction (arXiv:math/0403229, Lemma 2.4)
applied to `G / Gamma(4) = SL_3(Z/4)`. The image of `K_I` there is a Sylow
2-subgroup. The preimages of the Sylow 3- and 7-subgroups already have ranks in
`(1/3)Z` and `Z`, by the index bound against `Gamma(3)`.

**`K''`.** `K''` contains `Gamma(3)` with index 16, so `rk_{K''} in (1/16)Z`.
`Gamma(3)` is torsion-free, so the finite subgroups of `K''` embed in a group
of order 16. They are 2-groups, so their orders divide 8, and a conjugate of
`D_8` lies in `K''`, as above. The forward implication is the same argument.
For the converse, `8 rk_{K''} in Z` gives `rk_G in (1/2808)Z`, and
`gcd(2808, 43008) = 24`.

**Sharpness.** Let `H <= G` have finite index and put `b = v_2(lcm H)`. `D_8`
acts on `G/H`, and the stabilizer of `gH` is `D_8 cap gHg^(-1)`, a 2-subgroup of
a conjugate of `H`, of order dividing `2^b`. So every orbit, and hence `[G:H]`,
is divisible by `2^(3-b)`. Equality `b + v_2([G:H]) = 3` holds for `K_I` and
`K''`.
