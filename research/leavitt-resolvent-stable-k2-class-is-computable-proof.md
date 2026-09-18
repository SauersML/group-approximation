---
rg: 2
id: leavitt-resolvent-stable-k2-class-is-computable-proof
kind: route
title: Equality in the Steinberg groups is recursively enumerable, and every stable class is a unique explicit symbol
target: leavitt-resolvent-stable-k2-class-is-computable
requires:
  - leavitt-resolvent-k-theory-is-shifted-rational-k-theory
  - st-n-leavitt-resolvent-word-problem-reduces-to-k2
---

**Inputs.**
- **(WP)** `R_L` has solvable word problem in its six generators, and so does `E_N(R_L)` for `N >= 3`
  (`st-n-leavitt-resolvent-word-problem-reduces-to-k2`, item 1).
- **(K)** `ι : K_2(R_L) -> Q^x` is an isomorphism, and `ι{λ, N+1} = λ`
  (`leavitt-resolvent-k-theory-is-shifted-rational-k-theory`, items 3--4).
- **(Colim)** `St(R_L) = colim_M St_M(R_L)`, and `K_2(R_L) = ker(St(R_L) -> E(R_L))`, the colimit of the
  `K_2(M, R_L)`. So two elements of `St_N(R_L)` with the same stable class in `K_2(R_L)` become equal in `St_M(R_L)`
  for some finite `M >= N`.

**Recursive enumerability of equalities.**
- `St_M(R_L)` is presented by generators `x_ij(a)`, one for each `a in R_L`, and the relations
  `x_ij(a) x_ij(b) = x_ij(a + b)`, `[x_ij(a), x_jk(b)] = x_ik(ab)` for `i, j, k` distinct, and `[x_ij(a), x_kl(b)] = 1`
  for `j != k`, `i != l`.
- Represent elements of `R_L` by ring words. Two words name the same generator exactly when they are equal in `R_L`,
  which is decidable by (WP). So the relator set, taken over all word triples `(a, b, a + b)` and `(a, b, ab)`, is
  recursively enumerable, uniformly in `M`.
- Hence the set of pairs of `St_M(R_L)`-words that are equal in `St_M(R_L)` is recursively enumerable, uniformly in
  `M`. No finite presentation is needed.

**Item 1.**
- Let `w` be a word of `St_N(R_L)` with image `1` in `E_N(R_L)`. This can be checked by (WP). Then
  `w in K_2(N, R_L)`.
- Put `λ_0 = ι[w]`, with `[w]` the stable class. By (K), `[w] = [{λ_0, N+1}]`.
- By (Colim), `w = {λ_0, N+1}_M` in `St_M(R_L)` for some `M`. So some triple `(M, λ_0, d)` exists, and the search
  over the recursively enumerable set of triples finds a triple.
- Any triple `(M, λ, d)` found has `[w] = [{λ, N+1}]`, so `λ = ι[w] = λ_0` by (K). So the output is `ι[w]`.
- The words `{λ, N+1}_M` are computable from `λ`. `λ = a/b` is the ring word `a · (1/b)`, with
  `1/b = t_2 t_1^(b-1) A s_1^(b-1) s_2`. The symbol is `h_12(u v) h_12(u)^-1 h_12(v)^-1` with `u = λ`, `v = N + 1`,
  and `h_12(u) = w_12(u) w_12(-1)`, `w_12(u) = x_12(u) x_21(-u^-1) x_12(u)`. All inverses are explicit ring words.

**Item 2.** This is item 1, together with the fact that `ι` is injective.

**Item 3.**
- Under (i), `K_2(N, R_L) ≅ K_2(R_L) ≅ Q^x`. Item 3 of `st-n-leavitt-resolvent-word-problem-reduces-to-k2` then gives
  the word problem.
- Explicitly: a word `w` is `1` in `St_N(R_L)` if and only if its image in `E_N(R_L)` is `1` and item 1 returns
  `λ = 1`.
- Each `{λ, N+1}_N` lies in `K_2(N, R_L)` and has stable class `λ`. So under (i), `λ -> {λ, N+1}_N` is onto
  `K_2(N, R_L)`.

**Item 4.**
- `λ`, `μ` and `N + 1` lie in a commutative subring `C` of `R_L`. In `St_N(C)`, `N >= 3`, symbols of units are
  bimultiplicative (Dennis--Stein, LNM 342, §9(a), relation (S1), for commutative rings and `n >= 3`, as pinned
  earlier by gq-referee-b). So `{λμ, N+1}_N = {λ, N+1}_N {μ, N+1}_N` in `St_N(C)`, and hence in `St_N(R_L)`.
- The stabilization sends `{λ, N+1}_N` to `λ` under `ι`. So the map is a section, and `K_2(N, R_L) = U_N ⋊ Q^x`. It is a
  direct product if `K_2(N, R_L)` is central, which is open (`k2-central-in-steinberg-groups-of-leavitt-resolvent-ring`).
  The argument below needs only the factorization `w = u · {ι[w], N+1}_N` with `u in U_N`.
- A word `w in K_2(N, R_L)` is nontrivial if and only if `ι[w] != 1`, which is decidable by item 1, or its
  `U_N`-component `w · {ι[w], N+1}_N^-1` is nontrivial.
- With item 2 of the reduction node, the word problem is solvable if and only if nontriviality in `U_N` is
  recursively enumerable.
