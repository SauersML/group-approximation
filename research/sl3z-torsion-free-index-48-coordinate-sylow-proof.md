---
rg: 2
id: sl3z-torsion-free-index-48-coordinate-sylow-proof
kind: route
title: Pass to a congruence quotient, split its Sylow 2-subgroup into prime coordinates, and find one coordinate that sees no involution
target: sl3z-torsion-free-subgroups-have-index-divisible-by-48
requires:
  - sl3z-finite-index-subgroups-are-congruence-subgroups
  - sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48
---

Let `G = SL_3(Z)`, let `H <= G` be torsion-free of finite index, and put
`A_0 = diag(1,-1,-1)`.

**Step 0: 3 divides the index.** A finite subgroup `F <= G` meets every conjugate
of `H` trivially, so `F` acts freely on `G/H` and `|F|` divides `[G:H]`. Take `F` of
order 3, say the cyclic permutation matrices. The rest of the proof shows
`v_2([G:H]) >= 4`.

**Step 1: a finite problem.** By
[[sl3z-finite-index-subgroups-are-congruence-subgroups]], `H` contains some
`Gamma(m)`. Enlarging `m`, assume `m = 2^k m'` with `k >= 4` and `m'` odd. Put
`Q = H/Gamma(m)` inside

    SL_3(Z/m) = SL_3(Z/2^k) x prod_(q^e || m') SL_3(Z/q^e).

Let `P = P_2 x prod_q P_q` be a Sylow 2-subgroup, a product of Sylow 2-subgroups of
the factors. After conjugating `Q`, which conjugates `H`, some Sylow 2-subgroup `S`
of `Q` lies in `P`. Then `v_2([G:H]) = v_2([SL_3(Z/m) : Q]) = v_2([P : S])`, and
`[P:S]` is a power of 2.

Let `T` be the set of reductions mod `m` of the nontrivial torsion elements of
`G`. Since `Gamma(m)` is torsion-free (`m >= 3`) and `H` is torsion-free,
`Q cap T` is empty, and so is `S cap T`.

**Step 2: two local facts about involutions.**

*(a) Odd `q`.* All involutions of `SL_3(Z/q^e)` are conjugate to `A_0`. Let
`u^2 = 1`. Then `e_+ = (1+u)/2` and `e_- = (1-u)/2` are complementary idempotents,
so `(Z/q^e)^3 = V_+ + V_-` with both summands free over the local ring. Since
`det u = (-1)^(rank V_-) = 1` and `u != 1`, `rank V_- = 2`. So `u` is `GL_3`-conjugate
to `A_0`, and the centralizer `GL_1 x GL_2` of `A_0` has every determinant, so
`u` is `SL_3`-conjugate to `A_0`.

*(b) `p = 2`.* Every involution `u` of `SL_3(Z_2)` is `SL_3(Z_2)`-conjugate to `A_0`
or to `B_0 = [[0,1],[1,0]] (+) (-1)`. Both lie in `SL_3(Z)`.
- Let `L = Z_2^3`, `L^+ = ker(u - 1)`, which is pure, and `M = L/L^+`, which is free.
  `u` acts on `M` by `-1`, because `u(1+u)x = (1+u)x`.
- For lifts `x_j` of a basis of `M`, `ux_j = -x_j + lambda_j` with `lambda_j` in `L^+`.
  Changing a lift by `l` in `L^+` changes `lambda_j` by `2l`. So the `lambda_j`
  define an `F_2`-linear map `delta : M/2M -> L^+/2L^+`.
- Put `delta` in normal form by changing bases of `L^+` and `M`. Changes of basis
  over `F_2` lift to `Z_2`. Then adjust the lifts. `L` splits into `a` trivial
  lattices, `b` sign lattices and `c = rank delta` regular lattices
  `span(x_j, l_j)`, with `ux_j = -x_j + l_j`.
- For rank 3, `u != 1` and `det u = (-1)^(b+c) = 1`, the options are
  `(a,b,c) = (1,2,0)`, which gives `A_0`, or `(0,1,1)`, which gives `B_0`.
- The centralizers `diag(lambda,1,1)` of `A_0` and `1 (+) 1 (+) lambda` of `B_0`
  have every determinant, so `GL_3(Z_2)`-conjugacy is `SL_3(Z_2)`-conjugacy.

**Step 3: forbidden coordinate sets.** Let `F_2` be the set of reductions mod `2^k`
of the involutions of `G` that lie in `P_2`. For odd `q`, let `F_q` be the set of
involutions in `P_q`. Put `F = F_2 x prod_q F_q`, inside `P`.

`F` is contained in `T`. Let `x` be the image of an involution `g_0` of `G`, and let
each `y_q` be an involution. `g_0` has eigenvalues `1,-1,-1`, so by (a) there are
`k_q` with `y_q = k_q gbar_0 k_q^-1`. By surjectivity of `SL_3(Z) -> SL_3(Z/m)` there
is `z` in `G` with `z = 1 mod 2^k` and `z = k_q mod q^e` for every `q`. Then
`z g_0 z^-1` is an involution of `G` with image `(x, (y_q))`.

**Step 4: coordinate kernels.** For each coordinate `i` in `{2} u {q}`, put
`N_i = S cap P_i`, where `P_i` is embedded as the `i`-th coordinate. Suppose every
`N_i` meets `F_i`, say at `f_i`. The `f_i` lie in different coordinates, so they
commute and their product lies in `S cap F`, which is empty. So some `N_i` misses
`F_i`.

The kernel of the projection of `S` onto the other coordinates is `N_i`, so
`|S| <= |N_i| * |P| / |P_i|` and `[P : S] >= [P_i : N_i]`.

- **`i = q` odd.** `N_q` is a 2-group with no involution, so it is trivial, and
  `[P:S] >= |P_q|`. The kernel of `SL_3(Z/q^e) -> SL_3(F_q)` is a `q`-group, and
  `v_2(|SL_3(F_q)|) = v_2(q^2-1) + v_2(q-1) >= 4`. So `[P:S] >= 16`.
- **`i = 2`.** Let `W` be the preimage of `N_2` under `SL_3(Z_2) -> SL_3(Z/2^k)`.
  `W` is open and is a pro-2 group, since `P_2` is a 2-group and the kernel is
  pro-2. If `W` had torsion, some power of a torsion element would be an
  involution `u` in `W`.
  - By (b), `u = k A_0 k^-1` or `u = k B_0 k^-1` with `k` in `SL_3(Z_2)`.
  - Choose `k'` in `SL_3(Z)` with `k' = k mod 2^k`. Then `k' A_0 k'^-1` or
    `k' B_0 k'^-1` is an involution of `G` congruent to `u`.
  - So `u mod 2^k` lies in `N_2 cap F_2`, a contradiction, and `W` is torsion-free.

  By [[sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48]], 48 divides
  `[SL_3(Z_2) : W] = [SL_3(Z/2^k) : P_2] * [P_2 : N_2]`. The first factor is
  `|SL_3(Z/2^k)| / |P_2| = 21`, which is odd, so 16 divides `[P_2 : N_2]` and
  `[P:S] >= 16`.

In both cases `v_2([G:H]) = v_2([P:S]) >= 4`. With Step 0, 48 divides `[G:H]`.

**Consequence.** `l^2(G)` is `l^2(H)^[G:H]` as an `N(H)`-module, so a matrix over
`C[G]` restricts to a `[G:H]`-block matrix over `C[H]` and ranks scale by
`[G:H]`. The ranks obtained from Strong Atiyah on a family of subgroups lie in
`(1/gcd [G:H_i])Z`. 48 divides that gcd.
