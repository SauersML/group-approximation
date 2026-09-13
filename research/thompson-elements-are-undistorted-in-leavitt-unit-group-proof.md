---
rg: 2
id: thompson-elements-are-undistorted-in-leavitt-unit-group-proof
kind: route
title: Depth is subadditive and bounds the prefix change of every germ, while Thompson powers change prefixes linearly
target: thompson-elements-are-undistorted-in-leavitt-unit-group
requires: [binary-leavitt-unit-group-four-generated, thompson-v-powers-have-linearly-growing-slope]
---

Let `R = L_(F_2)(1,2)` and `R_N = span{ s_alpha t_beta : |alpha|, |beta| <= N }`.

1. **Subadditivity.** `t_beta s_gamma` equals `s_gamma'` if `gamma = beta gamma'`, equals
   `t_beta'` if `beta = gamma beta'`, and is `0` otherwise. So
   `s_alpha t_beta s_gamma t_delta` lies in `R_(N+M)` whenever the two factors lie in `R_N`
   and `R_M`. Hence `R_N R_M <= R_(N+M)`, and `ell(x) = min{ N : x in R_N }` satisfies
   `ell(xy) <= ell(x) + ell(y)`.
2. **Word length dominates depth.** `Q` is finitely generated
   (`binary-leavitt-unit-group-four-generated`). Fix a finite symmetric generating set `S`
   and put `L_S = max(1, max_(s in S) ell(s))`. By step 1, `|g|_S >= ell(g)/L_S` for every
   `g` in `Q`.
3. **Depth bounds prefix change.** `R` acts on the `F_2`-span of infinite sequences by
   `S[alpha]T[beta] e_(beta w) = e_(alpha w)`, and a Thompson unit `g` acts by
   `e_xi -> e_(g(xi))`. If `x` is in `R_N`, every basis vector in the support of `x e_xi`
   has the form `e_(alpha sigma^|beta| xi)` with `|alpha|, |beta| <= N`.
   - For aperiodic `xi`, the number `|alpha| - |beta|` is determined by `xi` and the output
     sequence. Two representations with different values would make two different shifts
     of `xi` equal, so `xi` would be eventually periodic.
   - So if a Thompson unit `g` lies in `R_N`, every germ of `g` at an aperiodic point
     changes prefix length by at most `N`.
   - Since germs are locally constant, the same bound holds at every point.
4. **Linear growth.** Let `g` in `V` have infinite order.
   - By `thompson-v-powers-have-linearly-growing-slope`, there are a periodic point `y_0`
     and constants `u, L >= 1` and `C` such that the germ of `g^z` at `y_0` changes prefix
     length by `e(z)`, with `|e(z)| >= L floor(z/u) - C`.
   - By steps 2 and 3, `|g^z|_S >= ell(g^z)/L_S >= (L floor(z/u) - C)/L_S`.
   - Negative powers are treated in the same way, using the periodic point supplied for
     `g^-1`.
5. **Conjugates.** `|h g^z h^-1|_S >= |g^z|_S - 2|h|_S`, so undistortion passes to conjugates.
6. **Corollary.**
   - Suppose `[a,b] = c` has infinite order, is central in `<a,b>`, and is conjugate into
     `V`. Then `c^(m^2) = [a^m, b^m]` gives `|c^(m^2)|_S <= 2m(|a|_S + |b|_S)`, contradicting
     step 5 for large `m`.
   - Suppose `t x t^-1 = x^k` with `|k| >= 2` and `x` conjugate into `V`. Then `x` has
     infinite order, and `|x^(k^j)|_S <= 2j|t|_S + |x|_S` contradicts step 5 for large `j`. ∎
