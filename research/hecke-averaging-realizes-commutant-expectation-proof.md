---
rg: 2
id: hecke-averaging-realizes-commutant-expectation-proof
kind: route
title: Kazhdan pair of the completion bounds the spherical numerical range of the lazy double-coset average
target: hecke-averaging-realizes-commutant-expectation
requires:
  - hecke-far-commutator-defect-formula
---

**Part 1 (structure).**  For `lambda in Lambda`, left multiplication
permutes the left cosets inside the double coset: `lambda w_i =
w_(sigma(i)) lambda_i` with `sigma` a permutation and
`lambda_i in Lambda`.  If `x` is `pi(Lambda)`-central then
`pi(lambda) (pi(w_i) x pi(w_i)^*) pi(lambda)^* = pi(w_(sigma(i))) x
pi(w_(sigma(i)))^*`, so `S(x)` is again `pi(Lambda)`-central.  Every
`x in pi(Gamma)' cap M` is fixed by each `Ad pi(w_i)`, hence by `S`.
Each `Ad pi(g)` is a unitary of `L^2(M)` acting as the identity on
`L^2(pi(Gamma)' cap M)`; a unitary fixing a closed subspace pointwise
preserves its orthocomplement, so `Ad pi(g)` commutes with the
orthogonal projection `E`, and so does the convex combination `S`.

**Part 2 (contraction).**  Fix a unitary `k in pi(Lambda)' cap M`.
Let `V subseteq L^2(M)` be the closed `Ad pi(Gamma)`-cyclic subspace
of `k`.  By the proof of `hecke-far-commutator-defect-formula`, the
positive definite function `psi_k` extends to the Schlichting
completion `G = PSL_n(Q_p)` (Shalom--Willis, Tzanev), and `V` is
`Gamma`-equivariantly identified with the GNS space of the extension:
`V` carries a continuous unitary `G`-representation `rho` with
`rho|_Gamma = Ad pi|_V` (the `rho(Gamma)`-orbit of `k` is dense in the
`rho(G)`-orbit by density of `Gamma` in `G`).  Write `K <= G` for the
compact open closure of `Lambda`; `k` is `Lambda`-fixed, hence
`K`-fixed by continuity.  Split `V = V^G oplus V_1` into `G`-invariant
vectors and their complement; as shown there, the projection of `k`
onto `V^G` is `E(k)`, so `k - E(k) =: xi_1 in V_1` and `xi_1` is
`K`-fixed (both `k` and `E(k)` are).

Under the completion, the coset decomposition `(HA1)` becomes
`K gamma_0 K = w_1 K sqcup ... sqcup w_L K` (the same representatives;
Tzanev).  Hence for every `K`-fixed `v in V`,

```text
(1/L) sum_i rho(w_i) v = T v,   T := rho(u_(K gamma_0 K)),      (HAP1)
```

the Hecke operator of the normalized `K`-bi-invariant probability
measure on `K gamma_0 K`.  The double coset is symmetric:
`gamma_0^(-1) = w_0 gamma_0 w_0^(-1)` for the signed permutation
`w_0 in Lambda` exchanging the first and last coordinates, so
`K gamma_0^(-1) K = K gamma_0 K` and `T` is self-adjoint on the
(`T`-invariant) subspace `V_1^K` of `K`-fixed vectors of `V_1`.

`G` has property (T) for `n >= 3` (Bekka--de la Harpe--Valette,
Thm 1.4.15), and every compact generating subset of a (T) group is a
Kazhdan set (ibid., Prop 1.3.2).  `Q_0 = K cup K gamma_0 K` is
compact, and it generates `G`: conjugating the integral elementary
subgroups `e_(ij)(Z_p) <= K` by powers of `gamma_0` and of
`gamma_0^(-1) = w_0 gamma_0 w_0^(-1)`, and moving slots by permutation
matrices in `K` (available since `n >= 3`), yields every `e_(ij)(a)`,
`a in Q_p`, and elementary matrices generate `SL_n(Q_p)`.  Let
`epsilon_0 > 0` be a Kazhdan constant for `(Q_0, epsilon_0)`.

`V_1` contains no nonzero `G`-invariant vector, so no unit vector of
`V_1` is `(Q_0, epsilon_0)`-invariant.  For a `K`-fixed unit
`v in V_1^K` and `g = kappa w_i kappa' in K gamma_0 K` with
`kappa, kappa' in K`, `rho(g) v - v = rho(kappa)(rho(w_i) v - v)`, so
`sup_(g in Q_0) || rho(g) v - v || = max_i || rho(w_i) v - v ||`.
Hence `max_i || rho(w_i) v - v || >= epsilon_0`, so

```text
(1/L) sum_i || rho(w_i) v - v ||^2 >= epsilon_0^2 / L,
Re <T v, v> = 1 - (1/(2L)) sum_i || rho(w_i) v - v ||^2
           <= 1 - epsilon_0^2 / (2L).                            (HAP2)
```

`T` is a self-adjoint contraction on `V_1^K` with numerical range in
`[-1, 1 - epsilon_0^2/(2L)]`, so the lazy operator restricted there,
`S|_(V_1^K) = (1 + T)/2` by `(HAP1)`, is self-adjoint with numerical
range in `[0, 1 - delta_0]`, `delta_0 := epsilon_0^2/(4L)`; for a
self-adjoint operator the norm is the numerical radius, so
`|| S|_(V_1^K) || <= 1 - delta_0`.

Finally `S` preserves `V` (it is a combination of `Ad pi(Gamma)`),
fixes `E(k) in V^G`, and preserves `V_1^K` (part 1 plus
`G`-invariance of `V_1`).  Iterating on `xi_1 = k - E(k) in V_1^K`:

```text
|| S^N(k) - E(k) || = || S^N(xi_1) || <= (1 - delta_0)^N ||xi_1||,
```

which is `(HA3)`; `(HA4)` follows because `E(k) = lim S^N(k)` and
`|| S^N(k) ||_2^2 = tau(S^N(k)^* S^N(k))` is a trace polynomial in
`k, k^*` and the `pi(w_i)`.  The constant `delta_0` depends only on
`(n, p)` through `epsilon_0` and `L`.
