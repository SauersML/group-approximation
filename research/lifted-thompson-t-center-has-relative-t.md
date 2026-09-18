---
rg: 2
id: lifted-thompson-t-center-has-relative-t
kind: claim
title: "The pair (T-bar, Z) has relative property (T): every cnd function on the lift T-bar of Thompson's T is bounded on its centre"
distinct_from:
  cantor-integer-maps-central-direction-has-relative-t: that asks relative (T) for (C(C,Z) ⋊ V, Z·1_C); this is the same statement for the subgroup T-bar, whose centre goes to Z·1_C. It is stronger and implies that claim.
  lifted-thompson-t-is-a-t-menable: that is the Haagerup property of T-bar; this claim refutes it
refuted_by:
  - lifted-thompson-t-is-a-t-menable
---

**Statement.** Let `T̄` be the lift of Thompson's `T` to `R`, and let `z(x) = x + 1`. For every
cnd function `ψ` on `T̄`, `sup_M ψ(z^M) < ∞`.

**Status.** OPEN.

**Why it matters.** It is a one-dimensional sufficient condition for refuting
`brin-thompson-groups-nv-are-a-t-menable`:
- it implies `cantor-integer-maps-central-direction-has-relative-t`, through
  `cantor-integer-maps-central-direction-via-lifted-thompson-t`;
- that implies `cantor-integer-maps-by-v-are-not-a-t-menable`, and hence that `2V` is not
  Haagerup.

**Evidence either way.**
- The class of the extension is bounded, since the rotation number gives `rot(z) = 1`.
- On the refuting side: bounded-class central extensions *can* have a relatively-(T) centre, as
  in lifts of lattices of `Sp(2n,R)`, but there the quotient has (T). No example with a
  Haagerup quotient is known to this lane. By arXiv:1905.10081, p. 96, the question whether
  Haagerup lifts through central extensions is open.
- On the supporting side: lattices in the universal cover of `SL_2(R)`, and the braid group
  `B_3`, which is the lift of `PSL_2(Z) ≤ T`, are Haagerup. There the centre is not relatively
  (T).
- A proof would need an invariant that sees the centre through cnd functions. Quasimorphisms do
  not qualify, since they are not cnd.

## Attempts

Earlier ruled-out witness classes are listed under `lifted-thompson-t-is-a-t-menable`, Attempts
2026-09-18: permutation representations on dyadic orbits, and virtual splittings.

- **2026-09-18 (swarm-0917-w9-w9-nv-break, reframing): dilation-tower reduction. The node stays
  OPEN.**
  - *Structure (proved).* `lifted-thompson-t-quotients-are-rotation-centralizers` shows
    `T̄/⟨z^{2^k}⟩ ≅ C_T(r_k)`, via `ι_k(g) = p(2^{-k} g(2^k ·))`, with `z ↦ r_k`.
  - *Reduction (proved).* `lifted-thompson-t-relative-t-forces-dyadic-twist-gap` puts the question
    in terms of a twist-cost function `c` on `R/Z`. It is lower semicontinuous, symmetric and
    subadditive, satisfies `c ≥ |e(θ)−1|/L`, and vanishes only at `0`.
    - `inf_{θ≠0} c = 0` refutes this node, by an explicit weighted sum of matrix-coefficient cnd
      functions.
    - The dyadic part of `c` is exactly `Gap_T`. This is a uniform spectral gap *inside Thompson's
      T* for the level-`k` copies `ι_k(S)`, on vectors with no `r_k`-fixed part.
  - *What this changes for a breaker.*
    - To refute this node it is enough to produce, from representations of `T` itself, vectors
      that are almost invariant under the `2^{-k}`-periodic copies of the generators and have no
      `r_k`-fixed part. Every representation of `T`, restricted to `C_T(r_k)`, is a candidate.
    - To prove this node, one needs `Gap_T` and also a way to handle non-dyadic twists, which is
      open. Subadditivity is useless for that, because `c` is only lower semicontinuous and
      `c(θ) ≳ |θ|`.
  - *Classes checked against `Gap_T` (heuristic kills, not full proofs).*
    - *Koopman representation on `L²(S^1)`, with Fourier vectors `e_n` for fixed `n`.* On each arc
      of length `2^{-k}`, `e_n` is within `O(n 2^{-k})` of a constant. So the defect of
      `ρ(ι_k(f̃)) e_n` tends to the *self-similar constant* `‖ρ(f)1 − 1‖²`, which is
      `∫ (√((f^{-1})') − 1)² > 0` for `f ≠ 1` in `F`. These vectors die at the rescaled-cell
      defect.
    - *Sums `Ψ = Σ a_k ψ_k ∘ ι_k` of pulled-back cnd functions of `T`.* Each summand is
      `2^k`-periodic along `z`, so an unbounded `Ψ` needs infinitely many levels. For Farley's
      `ψ`, recalled as comparable to caret count and not rechecked, both `ψ(r_k^M)` and
      `ψ(ι_k(t_1)) = ψ(r_{k+1})` are `≍ 2^k`. So finiteness on `S` forces `Σ a_k 2^k < ∞`, which
      bounds `Ψ` on `z`.
    - The invariant that kills this class is *rotation domination*:
      `sup_M ψ(r_k^M) ≤ C · Σ_s ψ(ι_k(s))` uniformly in `k`. Any family of cnd functions on `T`
      with this property is dead for this purpose.
    - *Induction from `λ(T̄) = C_{T̄}(t_1)`.* It halves twists, since
      `min(c(θ/2), c(θ/2+1/2)) ≤ √|S| Λ c(θ)` with `Λ = max_s |λ(s)|_S`. But inducing back up
      loses almost-invariance, because the subgroup has infinite index. So it gives no net descent.
  - *Next falsifiable step.* Test `Gap_T` on Jones' Pythagorean / planar-algebra representations of
    `T`, where rotations act by explicit unitaries. Either find rotation domination there, or find
    `r_k`-nonfixed vectors with defect `o(1)` under `ι_k(S)`.
