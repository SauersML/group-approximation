---
rg: 2
id: finite-scale-compressors-preserve-kazhdan-fixed-algebras
kind: claim
title: Mass transport replaces the ambient expander decomposition at the fixed-algebra level, so a compressor of a Kazhdan subgroup preserves its fixed algebra whenever the cluster sizes live on finitely many scales, with no period bound
distinct_from:
  bounded-cluster-period-preserves-kazhdan-fixed-algebras: that gets fixed-algebra invariance from a period bound on the dominant-target map, by building an ambient expander decomposition and applying Kun--Thom Proposition 3.1; this uses no period bound and no ambient decomposition, only that sigma(u) is a bijection of the finite sets and a scale hypothesis on cluster sizes, and it covers long cycles (the log-drift model of that node's remark) that no expander decomposition handles. The two hypotheses are incomparable.
  ambient-decomposition-kun-thom-normalization: that is the centralizer-level normalization given an ambient decomposition; this is the fixed-algebra level only, and it proves a one-sided-to-two-sided concentration lemma that replaces the ambient decomposition in the median step under a scale hypothesis, without deriving centralizer normalization.
  kt-counting-props-producers: that derives Concentrated from OneSided through blockRatio_negligible, which takes the ambient ExpanderDecomposition DG as an argument; item 3 here derives the same two-sided conclusion at one compressor from the one-sided inequality by mass transport, with a scale hypothesis on the observable in place of DG. It is paper mathematics, not Lean.
  bounded-period-compressors-carry-no-sofic-defect: that is the group-level kill of tame compressors, modulo KT*; this sharpens what a witness's wild compressor must do at the fixed-algebra level, and it does not kill any defect.
  component-space-sizes-miss-leavitt-cover-defect: that shows component-space sizes are compressor invariant on a cover where sigma(G) fixes the component algebra pointwise; this proves that invariance of the component algebra itself for arbitrary compressor groups, under a scale hypothesis.
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
  - experiments/scale-mass-transport-2026-09-17/mt_check.py
---

**ESTABLISHED.**

## Setting

This is the setting of `bounded-cluster-period-preserves-kazhdan-fixed-algebras`.
- `L` is a Kazhdan group with finite symmetric generating set `S`.
- `u` is an element of an ambient group with `u L u^-1 <= L`, and `H = <L, u>`.
- `sigma : H -> S_U` is a sofic representation, with lifts `sigma_n(g)` in `Sym(Y_n)`.
  Write `u_n = sigma_n(u)`.
- `Q_n = {Q_(n,i)}` is a cluster frame for `sigma|_L`. `pi_n(i)` is the dominant target
  and `ell_n(i)` the loss. Put `lambda_n = sum_i ell_n(i) / |Y_n|`. Item 1 of that node
  gives `lim_U lambda_n = 0`.
- `phi_n(y) = log |Q_n(y)|`, where `Q_n(y)` is the cluster containing `y`. Its
  distribution `nu_n` under the uniform measure on `Y_n` is the **log-size profile**.

Two scale hypotheses on the frame:

```text
(FS)   for every eps > 0 there are k and Lambda such that, for U-almost every n,
       some union of k intervals of length <= Lambda has nu_n-mass >= 1 - eps;
(LOG)  lim_U lambda_n log |Y_n| = 0.
```

`(FS)` says that the cluster sizes live, up to bounded factors, on finitely many scales,
which may move with `n`. It holds when the clusters have bounded size, and under `FD_k`.
It is incomparable with `BP_p`:
- a single long cycle of bounded-size clusters satisfies `(FS)` and fails every `BP_p`;
- clusters of sizes `2^m` for `0 <= m <= k_n`, each fixed by `pi_n`, satisfy `BP_1` and
  fail `(FS)` when `k_n -> infinity` with equal mass per level.

## Statement

1. **(Finite mass transport.)** Let `Y` be a finite set, `u` a permutation of `Y`,
   `phi : Y -> R`, and `a < b`, `eta > 0`. Let `E ⊆ Y` and `kappa : Y \ E -> [0, inf)`
   satisfy `phi(u y) >= phi(y) - kappa(y)` for `y ∉ E`. Then

   ```text
   eta · #{ y ∉ E : a <= phi(y) <= b - eta,  phi(u y) >= phi(y) + eta }
        <=  (b - a) |E|  +  sum_(y ∉ E) kappa(y).
   ```

   Applied to `-phi`: if `phi(u y) <= phi(y) + kappa(y)` for `y ∉ E`, then
   `eta · #{ y ∉ E : a + eta <= phi(y) <= b, phi(u y) <= phi(y) - eta }` has the same
   bound. The only input is `sum_y phi(u y) = sum_y phi(y)`, since `u` is a bijection.

2. **(Fixed-algebra invariance.)** Under `(FS)` or `(LOG)`, for every `g ∈ H`,

   ```text
   sigma(g) D_U^(sigma(L)) sigma(g)^-1 = D_U^(sigma(L)),
   ```

   and `D_U^(sigma(L)) = D_U^(sigma(u L u^-1))`. No period bound, no ambient expander
   decomposition and no property (T) of `H` is used.

3. **(One-sided concentration without an ambient decomposition.)** Let `f_n` be positive
   functions on the clusters, and `Bad_n` sets of clusters, such that

   ```text
   f_n(pi_n i) <= (1 + kappa_n) f_n(i)      for i ∉ Bad_n,  kappa_n -> 0,
   ```

   and let `X_n` be the set of points `y` that lie in a cluster of `Bad_n`, or satisfy
   `u_n y ∉ Q_(n, pi_n i)` for the cluster `Q_(n,i)` of `y`. Suppose
   `|X_n| = o(|Y_n|)`. Suppose also a scale hypothesis on `psi_n(y) = log f_n(Q_n(y))`:
   either
   - `(FS_f)`: `(FS)` with `psi_n` in place of `phi_n`; or
   - `(LOG_f)`: `psi_n` takes values in an interval of length `R_n` with
     `|X_n| R_n = o(|Y_n|)`.

   Then for every `c > 1`, the clusters `i ∉ Bad_n` with `f_n(pi_n i) < f_n(i)/c` have
   total weight `o(1)`. This is the two-sided conclusion (`Concentrated`) of
   `MedianVertexForm.blockRatio_negligible` at one compressor, obtained without its
   argument `DG : ExpanderDecomposition A T`.

4. **(Sharpness: the doubling tower.)** There are finite models with `lambda_n -> 0` in
   which `Ad(u_n)` moves a function constant on clusters a definite distance from the
   cluster-constant functions. So the loss bound and bijectivity alone do not give item 2.
   - Take levels `0 <= m <= k`, with `2^(k-m)` clusters of size `2^m` at level `m`.
   - `u` maps each pair of level-`m` clusters onto one level-`(m+1)` cluster, and the top
     cluster onto the level-`0` singletons.
   - Then `lambda ~ 1/(k+1) -> 0`, but `lambda log |Y| -> log 2`, and `(FS)` fails.
   - For random signs `g` in `D(Q)`, the distance `||g ∘ u^-1 - D(Q)||_1 / |Y|` stays near
     `1/2`.

   Here `u Q` strictly refines `Q`. So the constant in `(LOG)` is sharp up to a
   constant factor.

Derivation: `finite-scale-fixed-algebra-mass-transport-proof`.
