---
rg: 2
id: thompson-f-tensor-shift-pairs-have-bounded-commutator-ratio
kind: claim
title: Tensor-shift pairs for Thompson's F have commutator-to-relator ratio bounded uniformly in the support
distinct_from:
  thompson-f-exact-shift-covariant-models-force-amenability: that proves exact shift-covariant models force amenability and a support-dependent bound (5^(L-1) - 1); this is the L-uniform ratio bound it leaves open, stated for the honest finite pairs (a (x) 1, 1 (x) a).
  thompson-f-commutator-bound-holds-in-each-fixed-dimension: that bounds C_n(F) for each fixed n over all pairs; this asks for a bound uniform in the support L, but only for the tensor-shift subclass, whose dimension q^(L+1) is unbounded.
  thompson-f-is-not-hyperlinear: that is the full statement for all pairs; this is only the shift-covariant subclass and does not imply it.
artifacts:
  - experiments/thompson-f-shift-profile-2026-09-17/results.txt
  - experiments/thompson-f-shift-profile-2026-09-17/ratio_shift.py
  - experiments/thompson-f-shift-profile-2026-09-17/verify_ratio.py
  - experiments/thompson-f-shift-profile-2026-09-17/perturb.py
  - experiments/thompson-f-shift-profile-2026-09-17/shift_profile.py
  - experiments/thompson-f-shift-profile-2026-09-17/verify.py
---

**OPEN.** Let `F = <x_0, x_1 | R_1 = [x_0 x_1^-1, x_0^-1 x_1 x_0], R_2 = [x_0 x_1^-1, x_0^-2 x_1 x_0^2]>`, and
`e(U) = 2 - 2 Re tr_n U`. For each local dimension `q` there is `K_q < infinity` such that for every `L`
and every `a in U(q^L)`, the pair `X = a ⊗ 1_q`, `Y = 1_q ⊗ a` in `U(q^(L+1))` satisfies

```text
e([X, Y]) <= K_q^2 * max(e(R_1(X,Y)), e(R_2(X,Y))).
```

**Why it matters.** This would kill the tensor-shift class, the approximate Bernoulli models of
`thompson-f-exact-shift-covariant-models-force-amenability`, as a route to hyperlinearity of `F` at fixed
`q`. It would also rule the tensor shift out as the ratio-increasing doubling map `m -> 2m` that
the w19 fixed-dimension-constant census (lane swarm-0917-w19, not yet on main) asks for. It does not prove
`thompson-f-is-not-hyperlinear`.

**Proved part (product ansatz).** Let `a = u_1 ⊗ ... ⊗ u_L` be a full product with `u_k in U(q)`, and set
`u_0 = u_(L+1) = 1`.

- On site `k` (for `k = 1..L+1`), `X` acts by `u_k` and `Y` by `u_(k-1)`. So the pair is the tensor product
  of the one-site pairs `(u_k, u_(k-1))`.
- Every word `w` then evaluates to `⊗_k w(u_k, u_(k-1))`.
- `R_1`, `R_2` and `[x_0, x_1]` lie in `[F, F]`. So they are trivial on the two end sites, `k = 1` and
  `k = L+1`, whose pairs have an identity generator and hence generate abelian groups.
- `tr_n` is multiplicative on tensor products, so `1 - e(w)/2 = prod_(k=2..L) (1 - e_k(w)/2)`, where `e_k`
  is the value on the pair `(u_k, u_(k-1))` in `U(q)`.
- For `L = 2` this is exactly one `U(q)` pair, namely `(u_2, u_1)`, so `C ≤ C_q(F)`.
- For larger `L`, full products give a multiplicative combination of `U(q)` pairs. No bound on the ratio
  in terms of `C_q` is claimed for that case.

A general `a` is not a product. Its non-product part is exactly what the claim must control.

## Attempts

- **Numerical census** (swarm-0917-w20-w20-nh-break, 2026-09-20; best found, uncertified). See
  `experiments/thompson-f-shift-profile-2026-09-17/results.txt`.
  - For `q = 2` and `L = 2..5`, the best ratio is `C = 2.3803` with `e(c) = 3.4201`. It is identical at
    every `L`, and restarts and perturbations reach at most 2.3935.
  - The optimum is a product to 0.5% (op-Schmidt `[2, .0106, 0, 0]`). Its `U(2)` factor `(v, u)` alone
    gives 2.3797.
  - In the small-commutator regime (`||[X,Y]||_2 = 0.3`), `C` is 0.76–1.01.
  - For comparison, generic pairs reach `C_n ≥ 3.2286` for `n ≥ 4`.
- **Missing step.** A uniform-in-`L` control of non-product `a`. A candidate invariant is the operator
  entanglement of `a` across the cut. The optimiser drives it to about 0, but no inequality relating it to
  the ratio is known.
