---
rg: 2
id: deligne-maslov-tensor-functors-are-asymptotically-regular
kind: claim
title: Every tensor functor of a one-third Maslov model is asymptotically regular, so no bounded-level comparison can exist
distinct_from:
  deligne-maslov-sector-traces-are-central-regular: that classifies the traces on the twisted fibre A_omega; this applies it to point-norm models and to every tensor functor built from them, and turns it into a pointwise distance bound that kills every bounded-level (finite-image) comparison argument, including the tensor-cube reduction.
  deligne-parameter-group-is-a-virtual-invariant: that kills virtual descent through the divisibility set {1,2}; this kills the stability-comparison class through the trace, at a non-central element of a kernel, and says nothing about divisibility.
  sp4-quasirep-windings-budget-and-saturation: that constrains windings on one relator; this constrains traces at every non-central element and uses no relator.
  deligne-nontrivial-maslov-opnorm-sectors-are-empty: that is the open emptiness statement; this is a structural necessary condition any hypothetical model satisfies, and does not decide emptiness.
---

**ESTABLISHED** (route `deligne-maslov-tensor-functors-are-asymptotically-regular-proof`).

**Setting.** `Gamma = Sp_4(Z)`, with `b`, `E_infinity`, `P_op` as in `deligne-sep7-norm-parameter-closed-subgroup`,
and `omega = exp(2 pi i/3)`. A *`1/3`-model* is a sequence `U_n : Gamma -> U(d_n)`, `U_n(e) = I`, with
`||U_n(g)U_n(h) - omega^(b(g,h)) U_n(gh)|| -> 0` for every fixed pair; so `1/3 in P_op` iff one exists. `tr` is the
normalized trace, `Q = prod M_(d_n) / (+) M_(d_n)` the norm corona, and "non-central" means `g not in {+I, -I}`.

For integers `a, c >= 0` with `a + c >= 1` and any sequence `R_n : Gamma -> U(D_n)` (no condition on `R_n` at
all), the *tensor functor* `F_n = U_n^(x a) (x) conj(U_n)^(x c) (x) R_n`. When `R_n` is an asymptotic
`omega^(r b)`-model, `F_n` is an asymptotic `omega^((a - c + r) b)`-model. The tensor cube `a = 3, c = 0, R = 1` is
an honest asymptotic homomorphism of `Gamma`.

**Theorem.** Let `U_n` be any `1/3`-model, and let `F_n` be a tensor functor of it as above.

1. **Regular trace.** For every non-central `g in Gamma`, `tr U_n(g) -> 0`, hence `tr F_n(g) -> 0`.
2. **Distance to scalars.** For every non-central `g` and every sequence of scalars `mu_n in C`,

   ```text
   liminf_n || F_n(g) - mu_n I ||_2  >=  1,     and  >= sqrt 2  if |mu_n| = 1,
   ```

   in the normalized Hilbert--Schmidt norm, hence also in operator norm.
3. **No bounded-level comparison.** Let `rho_n : Gamma -> U(D'_n)` be arbitrary maps (on the same spaces as `F_n`)
   and `g` non-central. If `|| F_n(g) - rho_n(g) ||_2 <= eps` for infinitely many `n`, then
   `|tr rho_n(g)| <= eps + o(1)` along them. In particular:
   - if `rho_n(g) = I` for infinitely many `n`, then along them `|| F_n(g) - I ||_2 -> sqrt 2`, so the operator-norm
     distance is at least `sqrt 2 - o(1)`;
   - no `F` is `Q`-close (distance `< 1` at every element) to a homomorphism `Gamma -> U(Q)` whose image is finite,
     or to any sequence of honest representations of bounded level: every finite-index subgroup contains
     non-central elements, and they act trivially.
4. **What survives.** If `F_n` is pointwise HS-close (distance `eps < 1`) to honest representations `rho_n` of
   `Gamma`, then for every non-central `g`, `|tr rho_n(g)| <= eps + o(1)`. So along the sequence each non-central
   `g` eventually leaves `ker rho_n`: the `rho_n` must have unbounded level and asymptotically regular characters.

**What this changes.**
- The conditional in the w8 tensor-cube attempt on `deligne-finite-parameter-group-has-period-prime-to-three`
  ("if every tensor cube were `Q`-close to a hom with finite image, then `1/3 not in P_op`") has a hypothesis that
  is *equivalent to the flagship itself*: item 3 shows the hypothesis fails for every cube as soon as one
  `1/3`-model exists, and it holds vacuously otherwise. So that route is circular, not merely hard.
- The class killed: every argument that proves `1/3 not in P_op` by comparing some tensor functor of a model
  (cube, `U (x) conj U`, `U (x) R`, direct sums of these) with a representation that is trivial, scalar, or of
  bounded level on a finite-index subgroup — by stability, rigidity or averaging. The invariant is the
  central-regular trace of `deligne-maslov-sector-traces-are-central-regular`. The step where every member dies is
  the evaluation at one non-central element of the kernel, where the trace of the functor is `0` and that of the
  comparison is `1`. The kill holds in the tracial ultraproduct, so it covers HS-stability versions too.
- What any surviving comparison argument needs is an *unbounded-level*, asymptotically regular target, the regime
  of Dadarlat's matricial (not uniform, not finite-image) stability. That is where the w8 survivor now lives. A
  level-free argument that works in the uniform category is recorded, conditional on one citation, in the route.
