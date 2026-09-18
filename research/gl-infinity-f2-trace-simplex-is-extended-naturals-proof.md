---
rg: 2
id: gl-infinity-f2-trace-simplex-is-extended-naturals-proof
kind: route
title: Choquet--Thoma on a countable closed extreme set, the identity theorem for the rank generating function, and powers of zero extensions
target: gl-infinity-f2-trace-simplex-is-extended-naturals
requires:
  - gl-infinity-f2-extreme-characters-are-rank-powers
  - dlv-locally-inner-inducing-character-classification
  - jacobson-el-characters-are-symbol-or-finitary-extensions
  - ce-characters-closed-multiplicative-semigroup
---

## Imported facts

* **(I1)** `gl-infinity-f2-extreme-characters-are-rank-powers`: `Ch(L) = {sigma_m : m in N̄}`.
* **(I2)** Choquet--Thoma, from `dlv-locally-inner-inducing-character-classification`: every trace is the
  barycenter of a unique Borel probability measure on `Tr(G)` carried by `Ch(G)`. Here `Tr(G)` is compact
  and metrizable in the pointwise topology.
* **(I3)** Theorem A of `jacobson-el-characters-are-symbol-or-finitary-extensions`: every character of
  `E = EL_n(J)` is `sigma o p` or `e psi` with `psi in Ch(L) \ {1}`. Every such function is a character.
* **(I4)** `ce-characters-closed-multiplicative-semigroup`: `CE(E)` is closed under pointwise limits and
  pointwise products, and `δ_e in CE(E)` iff `E` is hyperlinear (item 4 with `N = {e}`).

Write `c(g) = rank(g-1)`. For every `c >= 0` there is `g_c in L` with `c(g_c) = c`: take the block sum of `c`
copies of `[[1,1],[0,1]]`.

## Part 1

**Continuity.** Fix `g` with `c = c(g)`. The function `f_c(m) = 2^(-mc)` on `N̄` is continuous.
* For `c = 0` it is constant `1`.
* For `c >= 1` it tends to `0 = f_c(∞)`.

So `Phi(mu)(g) = ∫ f_c dmu` is affine in `mu` and weak*-continuous for each `g`. Hence `Phi` is continuous
into the pointwise topology.

**Values are traces.** `Phi(mu)` is a norm-convergent countable convex combination of traces. Normalization,
conjugation invariance and positive-definiteness pass to such combinations.

**Surjective.** Let `tau in Tr(L)`.
* By (I2), `tau` is the barycenter of a probability `nu` on the countable set `Ch(L)`.
* Evaluation at `g` is continuous and affine, so `tau(g) = sum_m nu({sigma_m}) sigma_m(g)`.
* So `tau = Phi(mu)` with `mu({m}) = nu({sigma_m})`.

**Injective.** Suppose `Phi(mu) = Phi(mu')`. Put `F(x) = sum_(m<∞) mu({m}) x^m`, and define `F'` from `mu'`
in the same way; both are holomorphic on `|x| < 1`.
* Evaluating at `g_c` for `c >= 1` gives `F(2^(-c)) = F'(2^(-c))`, since the atom at `∞` contributes `0`.
* The points `2^(-c)` accumulate at `0`, so `F = F'` by the identity theorem.
* Hence `mu({m}) = mu'({m})` for `m < ∞`, and the atoms at `∞` agree because both measures have total
  mass `1`.

**Homeomorphism.**
* `Prob(N̄)` is weak* compact and `Tr(L)` is Hausdorff, so the continuous bijection `Phi` is a
  homeomorphism.
* The Dirac masses form a closed copy of `N̄` in `Prob(N̄)`, and `delta_(m_j) -> delta_m` iff `m_j -> m`.
  Their image is `Ch(L)`.
* The limit statement is continuity of `Phi^(-1)`. □

## Part 2

`2^(-mc) 2^(-lc) = 2^(-(m+l)c)`, also when `m` or `l` is `∞`: for `c >= 1` both sides are `0`, and for
`c = 0` both are `1`. Expanding the product of the two series gives `Phi(mu * nu)`. □

## Part 3

`c(t) = 1`, so `tau(t) = sum_(m<∞) mu({m}) 2^(-m)`.
* This equals `1` iff `mu = delta_0`, that is `tau = 1`.
* It equals `0` iff `mu = delta_∞`, that is `tau = δ_e`. □

## Part 4

**The characters.** By (I3) and Part 1, the non-symbol characters are `e sigma_m` with `sigma_m != 1`, that
is `m >= 1`. And `e sigma_∞ = e δ_e = δ_e`.

**Zero extensions multiply.** `(e psi)(e psi') = e(psi psi')`, since both vanish off `L`. So
`(e sigma_m)(e sigma_l) = e sigma_(m+l)` by Part 2, and `S + S ⊆ S` by (I4).

**`S` is closed.** If `m_j -> m` in `N̄`, then `e sigma_(m_j) -> e sigma_m` pointwise: on `L` by Part 1, and
off `L` all values are `0`. Apply (I4).

**`∞ in S` iff hyperlinear.** This is (I4) with `e sigma_∞ = δ_e`.

**A finite index forces `∞`.** If `m in S` is finite, then `jm in S` for all `j >= 1`, and `jm -> ∞`, so
`∞ in S`.

**Shape of `S`.** `S ∩ N` is an additive subsemigroup of the positive integers. By the elementary
numerical-semigroup fact, it contains every sufficiently large multiple of its gcd `d`. □
