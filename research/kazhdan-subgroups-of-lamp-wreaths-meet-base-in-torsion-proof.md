---
rg: 2
id: kazhdan-subgroups-of-lamp-wreaths-meet-base-in-torsion-proof
kind: route
title: Shrink a product Haar density on the dual lamp group and read off where invariant vectors live
target: kazhdan-subgroups-of-lamp-wreaths-meet-base-in-torsion
requires: []
artifacts:
  - research/kazhdan-subgroups-of-lamp-wreaths-meet-base-in-torsion.md
---

Notation as in `(LW1)`. Standard facts used:

- (F1) Definition of property (T): a countable group `K` has (T) if there are a
  finite `S <= K` and `eps > 0` such that every unitary representation with a
  unit vector `xi` satisfying `||pi(s) xi - xi|| < eps` for all `s in S` has a
  nonzero `K`-invariant vector (Bekka--de la Harpe--Valette, *Kazhdan's
  Property (T)*, Definition 1.1.3 and Proposition 1.2.1).
- (F2) Pontryagin duality for countable discrete abelian groups: the dual is a
  compact metrizable abelian group, and characters separate points
  (Hewitt--Ross, *Abstract Harmonic Analysis I*, Theorem 24.8 and 24.14).
- (F3) A closed subgroup of a compact group that has positive Haar measure is
  open, hence of finite index (Hewitt--Ross, Theorem 20.17 / Corollary 20.18 of
  the Steinhaus lemma).

## 1. The measures

`B^ = prod_{x in X} W^` with the product topology, a compact metrizable
abelian group. `Q` acts by `(q theta)_x = theta_{q^{-1} x}`. For
`b in B` with finite support `F`, the value `theta(b) = prod_{x in F} theta_x(b_x)`
depends only on the coordinates in `F`.

Fix a decreasing basis `U_1 > U_2 > ...` of open neighbourhoods of `0` in `W^`
(metrizability, F2). Let `m` be Haar probability measure on `W^`, and let
`nu_n = m(U_n)^{-1} m|_{U_n}`, which is defined since open sets have positive
Haar measure. Put `mu_n = nu_n^{(x) X}` on `B^`. Since `Q` only permutes
coordinates and all factors are equal, `mu_n` is `Q`-invariant.

## 2. The representations

On `H_n = L^2(B^, mu_n)` define

```text
(pi_n(b) f)(theta) = theta(b) f(theta),         b in B,
(pi_n(q) f)(theta) = f(q^{-1} theta),           q in Q.
```

Both are unitary: the first is multiplication by a function of modulus `1`,
the second is the Koopman operator of a measure-preserving map. With the
convention `(q b)_x = b_{q^{-1} x}`, one has `(q^{-1} theta)(b) = theta(q b)`.
So

```text
pi_n(q) pi_n(b) pi_n(q)^{-1} = pi_n(q b),
```

and `pi_n(b q) = pi_n(b) pi_n(q)` defines a unitary representation of
`G = B semidirect Q`.

## 3. The constant vector is asymptotically invariant

Let `g = b q in G`, and let `F` be the support of `b`. Since `pi_n(q) 1 = 1`,

```text
||pi_n(g) 1 - 1||^2 = integral |theta(b) - 1|^2 d mu_n
                    = integral_{(W^)^F} |prod_{x in F} theta_x(b_x) - 1|^2 d nu_n^{(x) F}.
```

The integrand is continuous on `(W^)^F` and vanishes at `0`. The measure
`nu_n^{(x) F}` is supported in `U_n^F`, which shrinks to `0`. So the integral
tends to `0` as `n -> infinity`, for each fixed `g`, and hence uniformly over
any finite subset of `G`.

## 4. Invariant vectors live on the annihilator

Let `K <= G` have (T), with Kazhdan pair `(S, eps)` from (F1). By Section 3
there is `n` with `||pi_n(s) 1 - 1|| < eps` for all `s in S`. So `pi_n|_K` has a
nonzero `K`-invariant vector `f`.

Suppose that `a in K cap B` has infinite order, with support `F`. Invariance
under `a` gives `(theta(a) - 1) f(theta) = 0` for `mu_n`-almost every `theta`.
So `f` vanishes almost everywhere outside

```text
Z_a = { theta in B^ : theta(a) = 1 }.
```

The map `chi_a : (W^)^F -> T`, `theta_F -> prod_{x in F} theta_x(a_x)`, is a
continuous character of the compact group `(W^)^F`, whose dual is `(+)_F W`.
Its image is a closed subgroup of `T`. That image is finite if and only if
`chi_a^N = chi_{Na}` is trivial for some `N >= 1`, that is (F2, characters
separate points) if and only if `Na = 0` for some `N`. Since `a` has infinite
order, the image is infinite, so `ker chi_a` has infinite index in `(W^)^F`.
By (F3) it has Haar measure `0`.

`nu_n^{(x) F}` has density `m(U_n)^{-|F|}` times the indicator of `U_n^F` with
respect to Haar measure on `(W^)^F`. So `nu_n^{(x) F}(ker chi_a) = 0`. Since
`Z_a` is the preimage of `ker chi_a` under the coordinate projection
`B^ -> (W^)^F`, we get `mu_n(Z_a) = 0`. Hence `f = 0` almost everywhere, a
contradiction.

So `K cap B` consists of elements of finite order.

## 5. Corollaries

1. If `W` is torsion-free, `B` is torsion-free, so `K cap B = 1`, and
   `K -> G/B = Q` is injective.
2. Let `M` be a torsion-free abelian `Q`-module with an injective `Q`-map
   `iota : M -> (+)_X W`. Then `(v, c) -> (iota v, c)` is an injective
   homomorphism `M semidirect Q -> W wr_X Q` carrying `M` into `B`. A Kazhdan
   subgroup `K` of `M semidirect Q` meets `M` in a torsion-free group whose
   image in `B` is torsion. So `K cap M = 1`.

Nothing about `Q` is used: it may be Kazhdan, sofic or arbitrary.
