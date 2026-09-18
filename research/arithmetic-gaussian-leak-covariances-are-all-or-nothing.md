---
rg: 2
id: arithmetic-gaussian-leak-covariances-are-all-or-nothing
kind: claim
title: Gaussian crossed-product firewalls for the arithmetic SL3 pair obey a zero-one law over their spherical covariance
distinct_from:
  binary-free-and-ordinary-coset-wreaths-share-hyperlinearity: that proves the single independent-Gaussian test with covariance 1_C is equivalent to hyperlinearity of the arithmetic HNN group; this puts every C-invariant covariance on the same footing, showing that any one nontrivial Gaussian test with a Connes-embeddable crossed product is enough, and that one covariance in the closed quasi-regular cone failing to embed is enough for the opposite conclusion.
  homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse: that is one particular one-directional firewall, the compact homogeneous quotient; this Gaussianizes every C-central observable of every Connes-embeddable crossed product and returns a covariance in the same set.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that is the one-directional firewall for the ordinary coset Bernoulli shift; this is a two-sided classification over the whole family of C-invariant Gaussian covariances.
  no-spherical-leak-in-matrix-ultraproducts: that states the enemy as a mixing spherical component of a vector in an ultraproduct commutant; this makes the enemy a commutative Gaussian crossed product whose one parameter is a K-biinvariant positive-definite function on SL3(Q_2).
---

ESTABLISHED (unreviewed). DERIVATION
[[arithmetic-gaussian-leak-covariance-dichotomy-proof]].

Put `A = SL_3(Z[1/2])`, `C = SL_3(Z)`, `G_2 = SL_3(Q_2)`, `K = SL_3(Z_2)`.

A *covariance* is a real-valued positive-definite function `psi` on `A`
with `psi(e) = 1` and `psi(c) = 1` for every `c in C`. It is then
`C`-biinvariant. Let `A ↷ (Omega_psi, gamma_psi)` be the Gaussian action:
a centered Gaussian process `(Y_a)_(a in A)` with `E[Y_a Y_b] = psi(a^-1 b)`,
on which `a` acts by `Y_b -> Y_(ab)`. Put

```text
CEcov = { psi covariance : L^infinity(Omega_psi) rtimes A is Connes embeddable }.
```

The constant covariance `psi = 1` belongs to `CEcov`, since it is the
trivial action on one Gaussian variable. Let `P_lambda` be the closure,
for pointwise convergence on `A`, of the convex hull of the real
coefficients

```text
a -> <lambda_(A/C)(a) eta, eta>,   eta in ell^2_R(A/C),  ||eta|| = 1,  eta C-invariant.
```

`1_C` lies in `P_lambda` (take `eta = delta_C`), and so do the coefficients
of normalized indicators of `C`-invariant balls in the dyadic building.

**Theorem.**

- **(Z1) Closure.** `CEcov` is convex and closed under pointwise
  convergence on `A`.
- **(Z2) Gaussianization.** Let `A ↷ (B,tau)` be a trace-preserving action
  with `B rtimes A` Connes embeddable. Let `x = x* in B^C` with
  `tau(x) = 0` and `||x||_2 = 1`. Then
  `psi_x(a) = tau(x alpha_a(x))` belongs to `CEcov`.
- **(Z3) Leak.** If `psi in CEcov` and `psi != 1`, the unitary
  `exp(i Y_e)` is `C`-central but not `A`-central in a canonical embedding
  of `L(A)` into a tracial matrix ultraproduct. Hence the arithmetic HNN
  group `A *_C (C x Z)` is hyperlinear, and `(PTS1)` of
  `projective-trace-square-transfer-for-sl3-pair` fails.
- **(Z4) Zero-one law.** Exactly one of the following holds.
  - `CEcov = {1}`. Equivalently `(PTS1)` holds, and the arithmetic HNN
    group, the double `A *_C A`, and the coset wreaths are all
    nonhyperlinear.
  - `CEcov` contains `P_lambda` and `psi_x` for every observable `x` as in
    (Z2). Equivalently `(PTS1)` fails.

So each single covariance `psi_0 in P_lambda \ {1}` is a complete test:
- if `L^infinity(Omega_(psi_0)) rtimes A` is not Connes embeddable, the
  arithmetic HNN group is nonhyperlinear;
- if it is Connes embeddable, the group is hyperlinear.

The previous test `psi_0 = 1_C` is one member of this family.

**Spherical reading.** A covariance is the same thing as a real
`K`-biinvariant positive-definite function on `G_2` with value 1 at `e`.
The reason is that `A/C = G_2/K` and `C\A/C = K\G_2/K` by density. By Godement's theorem for
Gelfand pairs, the whole parameter is therefore a normalized positive
measure on the positive-definite spherical dual of `(G_2, K)`. Only the correspondence of double cosets is used in the proof.
The spectral description, and the identification of `P_lambda` with the
tempered spherical measures, are remarks and are not part of the
established statement.

## What it changes

- A positive attack (proving `(PTS1)`) may choose its test covariance
  freely inside `P_lambda \ {1}`, for example one with spread-out
  correlations over building balls, instead of the independent lamps
  `1_C`.
- A refutation may use any Connes-embeddable crossed product with a
  `C`-central observable. Its Gaussian shadow already refutes.
- No choice of a smoother or more mixing Gaussian firewall inside
  `P_lambda` can be strictly easier to embed than the coset Gaussian.
  All of them have the same truth value.

Covariances outside `P_lambda` (non-tempered, for example the
homogeneous-quotient covariance) are only one-directional firewalls here.
Whether `CEcov != {1}` forces all of them is not claimed.
