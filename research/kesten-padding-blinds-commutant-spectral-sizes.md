---
rg: 2
id: kesten-padding-blinds-commutant-spectral-sizes
kind: claim
title: Spectral-multiplicity sizes of the commutant averaging operator are Kesten-determined at quadratic scale and padding-destroyed below it
distinct_from:
  wold-multiplicity-blinds-commutant-packing-sizes: that fences 2-norm packing counts of op-norm-bounded approximate-commutant microstates; this fences eigenvalue counts of the averaging operator itself, which count dimension rather than bounded 2-norm mass, and which that node lists as an unfenced escape.
  commutant-density-trace-blind: that computes normalized dimensions of exact commutants; this identifies the whole quadratic-scale spectral distribution of the approximate-commutant averaging operator with the Kesten measure of (Gamma, S), and shows that below quadratic scale no spectral count is an invariant of sigma.
  kazhdan-commutant-compression-stability-is-finitary: that turns normalization into a uniform finite-dimensional inequality; this shows that eigenvalue counting of the averaging operator cannot supply the size in that inequality.
---

**ESTABLISHED (fence).** Proof: `kesten-padding-commutant-spectral-proof`.

## Setting

- `Gamma <= G` countable, `u in G` with `u Gamma u^-1 <= Gamma`, and `s_1, ..., s_m` generating
  `Gamma`. Put `S = {s_i^(+-1)}`.
- `sigma: G -> U(M^omega)`, `M^omega = prod_omega M_(d_n)`, is trace-preserving:
  `tau(sigma(g)) = 0` for `g != 1`.
- A *lift* is a sequence of free-group homomorphisms `sigma_n: F(s_1..s_m, u) -> U(d_n)` with
  `(sigma_n(w))_n = sigma(w)` in `M^omega` for every word `w`.
- `H_n = M_(d_n)` with inner product `tr(y^* x)`, and `Tr_H` is the unnormalized trace on
  `B(H_n)`. Hence `Tr_H(Ad v) = |Tr v|^2`.
- The averaging operators are
  `Phi_n = (1/2m) sum_i (Ad sigma_n(s_i) + Ad sigma_n(s_i)^*)` for `Gamma`, and
  `Phi^B_n` for `u Gamma u^-1`, with the letters `sigma_n(u) sigma_n(s_i) sigma_n(u)^-1`.
  Both are self-adjoint contractions of `H_n`.
- `N_n(eta) = rank 1_[1-eta,1](Phi_n)`, and `N^B_n(eta)` is the same count for `Phi^B_n`.
- For a normalizing scale `f(d_n)`, the *spectral profile* is
  `nu^f(eta) = lim_omega N_n(eta) / f(d_n)` in `[0, infinity]`, and `nu^(B,f)` is its `B`
  analogue.

By Courant--Fischer, `N_n(eta)` is the largest dimension of a subspace `V <= H_n` with
`(1/4m) sum_(s in S) ||[sigma_n(s), x]||_2^2 <= eta ||x||_2^2` for all `x in V`. So `N_n` counts
the dimension of the approximate commutant, which is the escape named in
`wold-multiplicity-blinds-commutant-packing-sizes`, Scope.

## Statements

**(SK1) Exact invariance.** `Phi^B_n = T_n^-1 Phi_n T_n` with `T_n = Ad sigma_n(u)^-1` unitary
on `H_n`. So `Phi_n` and `Phi^B_n` have the same spectrum with multiplicity, for every lift and
every `n`, and every unitarily invariant spectral quantity agrees on the two sides.

**(SK2) Kesten determination at quadratic scale.** Let `mu_(Gamma,S)` be the spectral measure of
`lambda(mu_S) = (1/2m) sum_i (lambda(s_i) + lambda(s_i)^*)` on `l^2(Gamma)` at `delta_e`: the
Kesten measure of the simple random walk.
- For every lift, the normalized spectral measures `d_n^-2 sum delta_(lambda_j(Phi_n))` converge
  weakly along `omega` to `mu_(Gamma,S)`.
- More generally, for every `g_1, ..., g_k in G`,
  `lim_omega d_n^-2 Tr_H(Ad sigma_n(g_1) ... Ad sigma_n(g_k)) = tau_(L(G))(lambda(g_1 ... g_k))`.
  So the joint distribution of `{Ad sigma_n(g)}` under `d^-2 Tr_H` is that of `lambda_G` in
  `(L(G), tau)`, for every trace-preserving `sigma`.
- If `(Gamma, S)` has Kazhdan constant `kappa > 0` and `Gamma` is infinite, put
  `c = kappa^2 / (2m)`. For every `eta < c` and every family `Y_n` in `B(H_n)` with
  `||Y_n|| <= 1`:

  ```text
  lim_omega d_n^-2 Tr_H( 1_[1-eta,1](Phi_n) Y_n ) = 0,
  ```

  and the same holds on the `B` side. In particular `nu^f(eta) = 0` whenever
  `lim_omega f/d^2 > 0`.
- For infinite `Gamma` without (T), `nu^(d^2)(eta) = mu_(Gamma,S)([1-eta, 1])` at continuity
  points. This tends to 0 as `eta -> 0` and is independent of `sigma`, `G` and `u`.

**(SK3) Padding.** Let `(sigma_n)` be any lift, and let `k_n` be integers with
`k_n / d_n -> 0`. There is a lift `(sigma'_n)` on `C^(d_n + k_n)` of a representation `sigma'`
with the following properties:
- It is carried to `sigma` by the canonical isomorphism
  `prod_omega M_(d_n + k_n) = prod_omega M_(d_n)`. So `A`, `B`, the Wold shift `D` and every
  invariant of `(M^omega, sigma)` are unchanged.
- It satisfies

  ```text
  N'_n(eta) >= N_n(eta) + k_n^2 (2x - x^2) - 2 k_n,   x = min(1, arccos(1 - eta)),   for all eta in (0, 1].
  ```

  The same bound holds for `N'^B_n`, by SK1.

  Keep the same normalizing sequence `f_n = f(d_n) > 0`. If `lim_omega f_n/d_n^2 = 0`, choose
  `k_n = ceil( (f_n d_n^2)^(1/4) )`. Then `k_n/d_n -> 0` and `k_n^2/f_n -> infinity`, so
  `nu'^f(eta) = nu'^(B,f)(eta) = +infinity` for every `eta > 0`.

## What this kills

Take the *spectral-multiplicity transcription* of the Hamming proof, for
`hyperlinear-groups-kill-rigid-compression-defects`. Measure `A = sigma(Gamma)' cap M^omega` and
`B = sigma(u) A sigma(u)^*` by eigenvalue counts of their averaging operators at a scale `f`.
Then argue that a nonzero Wold shift `D` forces a strict increase `nu^B > nu^A`, while conjugation
makes the two equal.

Along `omega`, either `lim f/d^2 > 0` or `lim f/d^2 = 0`, and every member dies:

- **`lim f/d^2 > 0`.** The counts are functions of `mu_(Gamma,S)` alone (SK2), identically 0 near
  eigenvalue 1 under (T). No quantity built from the near-1 spectral projections registers at
  this scale, including relative-position traces `Tr(E_A T E_A T^-1)`, principal angles and
  Jones-type indices. It cannot see `sigma`, `G`, `u` or `D`.
- **`lim f/d^2 = 0`.** The counts are not invariants of `sigma`. They depend on the lift, and a
  padded lift of the same `sigma` makes both profiles `+infinity` at every `eta` (SK3). So no
  inequality between `nu^A` and `nu^B` that holds for all lifts can use finiteness of `nu^A`. The
  Hamming skeleton needs exactly that finiteness to turn containment plus equality into equality.

The named invariant is the *dimension--mass gap*. Eigenvalue counts weigh a vector by its
dimension, while the ultraproduct weighs it by its 2-norm mass. An idle corner of relative size
`k/d -> 0` has zero mass and `k^2` dimensions.

## Scope and escapes

- This does not show that normalization fails, and it uses no property of `G` or of the
  compressor.
- **Remaining escape: lift-optimized counts.** For example,
  `inf over lifts of lim_omega N_n(eta)/f(d_n)`, or counts over lifts whose conjugation action has
  a uniform finite-stage spectral gap on the orthocomplement of the near-fixed space.
  - Padding only raises counts, so it does not touch an infimum.
  - Such a count is a finite-stage stability statement about lifts, not a size of the limit data.
  - It belongs with the exactification attempts on the target claim.
- Spectral data of operators that are not built from `Ad sigma_n(g)`, for example orbital or
  1-bounded entropy with baselines subtracted, are not covered.
