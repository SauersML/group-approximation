# HS coarse actor gap: liftable masas and the aspect-scale bound (2026-09-12)

Lane `nh-h2-coarse-gap`. Target: (H2') of `hs-normalization-needs-coarse-actor-scale-pinning`,
the coarse actor gap behind `kt-centralizer-normalization-hs`.

## Summary

1. **(H2') is a lifting problem, not a gap problem.** Established as
   `hs-block-gap-iff-liftable-masa-of-actor-commutant`. Take `S` a generating set of vertex
   generators and strict compressors, with Kazhdan constant `kappa_S`.
   - (H2') in the consumed form (F2), with vanishing summed boundary, holds if and only if
     `sigma(G)' cap prod_U M_n` has a maximal abelian subalgebra that is an ultraproduct of
     finite partition algebras (a *liftable masa*).
   - The gap constant is `kappa_S`.
   - The clause asking blocks to commute with the aspect-ratio observables is automatic
     under (H1).
2. **No actor gap is needed when the aspect profile occupies few scales.** Established as
   `ccr-under-vertex-rounding-from-few-aspect-scales`.
   - Under (H1), `eps_n <= 18 (N_n delta_n)^(1/3)`. Here `N_n` is the number of occupied
     dyadic windows of `zeta_A` and `delta_n` the uniform transport defect of item 4 of
     `vertex-rounding-reduces-ccr-to-commutant-excess`.
   - So (CCR) holds whenever `N_n delta_n -> 0`, for instance when the transported rounding
     defect is `o((log n)^(-3))`.
   - A counterexample to (CCR) under (H1) must occupy at least of order `1/delta_n` dyadic
     scales.
3. **Not settled.** (H2') is not proved for the Theorem E actors, and no cascade model was
   constructed. Both remaining questions are recorded below.

## 1. Why the gap is free

Property (T) acts at the ultraproduct level. `Ad sigma` is a genuine unitary representation
of `G` on `L^2(M)`, so `||x - E_Q x||_2 <= kappa_S^(-1) max_s ||[sigma(s), x]||_2` for every
`x in M`.
- If `C` is a masa of `Q` and `x` commutes with `C`, bimodularity of `E_Q` puts `E_Q x` in
  `Q cap C' = C`.
- So on the block-diagonal algebra `C' cap M`, the conditional expectation onto the blocks
  is already the Kazhdan projection. That is the scalar block gap, with constant `kappa_S`.
- The finite-stage form (F2) is its ultraproduct shadow. The one bookkeeping input is the
  random-sign identity: the summed boundary `sum_A ||[u, q_A]||_2^2` is the expected
  commutator of a random-sign block observable. It turns "vanishing boundary" into
  "`prod_U C_n <= Q`" and "block diagonal in the limit" into "`prod_U (C_n' cap M_n)`".

This generalizes the exact-centralizer-capture paragraph of
`hs-one-level-expander-block-decomposition`. Capture is one way to produce a liftable masa,
by minimal projections of exact centralizers, but the block gap needs only some liftable
masa of `Q`.

## 2. The aspect-scale bound

- **Trace conservation.** For each fixed scale `a`, `F_a(zeta_B) - F_a(zeta_A) >= 0`. Its
  trace equals `tau(F_a(zeta_B) - sigma_n(t) F_a(zeta_A) sigma_n(t)^*)`, because conjugation
  preserves the trace, so it is at most `delta_n`.
- **One window.** On the window `[a, 2a)`, a jump by the factor `1+c` raises `F_a` by at
  least `c/15`. So each window carries jump mass at most `15 delta_n / c`.
- **Many windows.** Summing over the `N_n <= 2 log_2 n' + 2` occupied windows and applying
  the excess lemma gives the bound.

The mechanism is a telescoping cascade. Take `L` levels in which restriction merges siblings.
Its per-scale trace discrepancy is `1/L`, while every level jumps. The bound shows this is the
only way (CCR) can fail under (H1): the jump must be spread thinly over at least of order
`1/delta_n` scales.

**Rate chain for `delta_n`.** This is item 4 of the vertex-rounding claim with constants.
- **Almost-invariant vector.** The transported rounding defect `eps'_n` makes the off-diagonal
  unit `w` of `pi~_n (+) pi_n` almost invariant under `Lambda`.
- **Kazhdan projection.** It gives an intertwiner `x` with `||x - 1||_2 <= eps'_n / kappa`.
- **Polar part.** It loses trace at most `2 eps'_n / kappa`.
- **Multiplicities.** Types whose multiplicities differ by more than `1+c` carry trace at
  most `4 eta / c`.
- **Optimize.** With `c = eta^(1/3)`, `delta_n <= 10 (eps'_n / kappa)^(1/3)`.

## 3. Cascades and liftability (heuristic, not a claim)

- **The cascade.** Take a uniform cascade: the level observable `h = log zeta_A / L` has
  order-one variance, and `sigma_n(t)` shifts it by about `1/L` on most mass. Then `h` lies in
  `Q cap prod_U Z(A_n)`, which is contained in `Z(Q)` and so in every masa of `Q`.
- **Coarse resolution.** A partition algebra containing `h` in the limit resolves `h` at some
  scale `w_n`.
  - If `L w_n -> infinity`, the boundary is about `1/(L w_n) -> 0`, but inside blocks the
    rescaled level observable `(h - c_A)/w_n` spans `L w_n` levels.
  - That observable commutes with the blocks and lies in `Q` (its commutator is about
    `1/(L w_n)`), but it is not constant on blocks.
  - So the partition is not maximal.
- **Fine resolution.** If `w_n` is of order `1/L` or smaller, `sigma_n(t)` moves most blocks off
  themselves, and the boundary is of order one.
- **Conclusion.** In a uniform cascade, `Q` has no liftable masa, and (H2') fails. That is
  consistent with the equivalence and the cascade profile.

## 4. What a proof of (H2') for the Theorem E actors must do

- **Lift a masa.** Lift a masa of `sigma(G)' cap M`, which necessarily contains
  `Q cap prod_U Z(A_n)`, to finite partitions with vanishing summed boundary. Equivalently,
  exclude finite-stage Hilbert-hotel shifts of central aspect observables by the compressors.
- **Or bound the scales.** Alternatively bound `N_n delta_n`, or the log-trace discrepancy
  `D_n = tau(log zeta_B) - tau(log zeta_A)`, where
  `tau(log zeta_A) = log n' - H(p) - 2 sum p_i log d_i`. That gives (CCR) directly, with no
  actor input.
- **Where (T) fails to help.** Property (T) of `G` cannot supply either statement by itself.
  It acts on the ultraproduct, where the cascade observable is exactly invariant. Any proof
  must use finite-stage structure of the models, such as rounding rates, quantitative
  stability, or monomiality.

## 5. Construction side

No cascade model for a Theorem E actor was built, and no numerics were run. A model needs:
- vertex rounding (H1);
- transport defect `delta_n` with `N_n delta_n` not tending to `0`, i.e. an aspect-ratio
  profile over at least of order `1/delta_n` dyadic scales, which needs `delta_n` at least of
  order `1/log n`;
- no actor rounding, since genuine `G`-models satisfy (CCR);
- a central level observable shifted by `sigma_n(t)` at scale about `1/N_n`.
