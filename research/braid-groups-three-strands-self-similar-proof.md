---
rg: 2
id: braid-groups-three-strands-self-similar-proof
kind: route
title: B_3 is self-similar through conjugation by diag(2,1) on its PSL_2(Z) quotient and halving on its center
target: braid-groups-on-at-most-three-strands-are-self-similar
requires: []
---

## 0. The virtual-endomorphism criterion

Let `G` be a group, `H <= G` of index `d`, and `F : H -> G` a homomorphism.
Its **core** is the largest subgroup `K` that is normal in `G`, contained in
`H`, and satisfies `F(K) <= K`. Nekrashevych (*Self-similar groups*, AMS 2005,
§2.5–2.7) and Nekrashevych–Sidki build from `(H, F)` a state-closed action of
`G` on `T_d`, transitive on the first level. It uses a transversal of `H`, and
`F` is the section map at one first-level vertex.

The kernel `N` of that action is contained in the core, and this direction is
all we use:
- `N` is normal;
- `N` fixes the first level, so it lies in the vertex stabilizer `H`;
- sections at that vertex of elements acting trivially act trivially, so
  `F(N) <= N`.

So a trivial core gives a faithful action.

For `B_2 = Z`, take `H = 2Z` and `F(2k) = k`. A core `K = mZ` with `m >= 1`
contained in `2Z` has `F(m) = m/2` not in `mZ`, so the core is trivial. `B_1`
is trivial.

## 1. Setup for B_3

- `B_3 = < a, b | a^2 = b^3 >`, with `a = sigma_1 sigma_2 sigma_1 = Delta` and
  `b = sigma_1 sigma_2`.
- `z = a^2 = Delta^2` generates the center `Z(B_3)`; for the amalgam
  `Z *_Z Z` the center is the amalgamated subgroup.
- `B_3 / <z> = < a, b | a^2 = b^3 = 1 > = Z/2 * Z/3`, which is isomorphic to
  `PSL_2(Z)`. The standard map is `sigma_1 -> ±[[1,1],[0,1]]`,
  `sigma_2 -> ±[[1,0],[-1,1]]`, so `a -> ±[[0,1],[-1,0]]` (order 2) and
  `b -> ±[[0,1],[-1,1]]` (order 3).
- Write `pi : B_3 -> PSL_2(Z)` for the quotient map; its kernel is `<z>`.
- `Lambda` is the image of the principal congruence subgroup `Gamma(2)` in
  `PSL_2(Z)`. It is free of rank 2 and has index 6, the quotient being
  `SL_2(Z/2) = S_3`.
- `Gamma_0(2) = { [[a,b],[c,d]] in SL_2(Z) : c even }` contains `Gamma(2)`.
- `D = diag(2,1)` and `c_D(A) = D A D^-1`, so
  `c_D([[a,b],[c,d]]) = [[a,2b],[c/2,d]]`. This maps `Gamma_0(2)` into
  `SL_2(Z)` and fixes `-I`, so it induces an injective homomorphism
  `c : Lambda -> PSL_2(Z)`.

## 2. The virtual endomorphism

- `P = pi^-1(Lambda)` has index 6.
- `Lambda` is free, so choose a homomorphism `s : Lambda -> P` with
  `pi o s = id` (lift two free generators). Then `s(Lambda) ∩ <z> = 1`, and
  since `z` is central, `P = s(Lambda) x <z>`.
- `H = s(Lambda) x <z^2>` has index 12 in `B_3`.
- Choose a homomorphism `F_0 : Lambda -> B_3` with `pi o F_0 = c` (lift
  `c(u), c(v)` for free generators `u, v`).
- Define `F : H -> B_3` by `F( s(lambda) z^(2k) ) = F_0(lambda) z^k`. It is a
  homomorphism because `z` is central, and `pi o F = c o pi` on `H`.

## 3. The core of F is trivial

Let `K` be normal in `B_3`, with `K <= H` and `F(K) <= K`.

1. **Image in PSL_2(Z).** `pi(K)` is normal in `PSL_2(Z)` and lies in
   `pi(H) = Lambda`. Also `c(pi(K)) = pi(F(K)) <= pi(K)`. By induction, every
   `A = ±[[a,b],[c,d]]` in `pi(K)` has `D^k A D^-k = ±[[a, 2^k b],[c/2^k, d]]`
   integral for all `k >= 0`. So `c = 0`, `ad = 1`, and
   `pi(K) <= U = { ±[[1,m],[0,1]] }`.
2. **No normal subgroup inside U.** A nontrivial normal subgroup of
   `PSL_2(Z)` contained in `U` would contain `±[[1,m],[0,1]]` with `m != 0`,
   hence its conjugate by `±[[0,1],[-1,0]]`, which is `±[[1,0],[-m,1]]` and is
   not in `U`. So `pi(K) = 1`, and `K <= <z> ∩ H = <z^2>`.
3. **Center.** `K = <z^(2t)>` for some `t >= 0`, and `F(z^(2t)) = z^t` must lie
   in `<z^(2t)>`. This forces `t = 0`.

So the core is trivial. By §0, `B_3` acts faithfully and state-closedly on
`T_12`, transitively on the first level. `∎`

## Remarks

- **Model test.** Drop the halving and use `F(s(lambda) z^k) = F_0(lambda) z^k`
  on `P`. Then `<z>` is a nontrivial invariant normal subgroup, and the core
  contains the center. Conversely, keep the halving but replace `F_0` by `s`,
  i.e. `c` by the identity. Then `F` is the identity on
  `[P,P] = [s(Lambda), s(Lambda)]`. That subgroup is characteristic in the normal
  subgroup `P`, so it is normal in `B_3`, lies in `H`, and is invariant, and the
  core contains it. Both ingredients are needed.
- **Why this stops at three strands.** For `n >= 4`, `B_n / Z(B_n)` has
  abstract commensurator `Aut(B_n/Z)` (Korkmaz), and injective virtual
  endomorphisms are restrictions of automorphisms. No contraction like
  `c_D` exists; see `braid-groups-on-four-or-more-strands-are-not-self-similar`.
