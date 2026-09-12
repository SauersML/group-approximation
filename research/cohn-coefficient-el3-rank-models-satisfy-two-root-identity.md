---
rg: 2
id: cohn-coefficient-el3-rank-models-satisfy-two-root-identity
kind: claim
title: Every characteristic-two rank model of EL_3 over the binary Cohn algebra satisfies N_23 N_12 = 0
distinct_from:
  rank-models-of-el3-satisfy-the-two-root-identities: that is the gate over simple algebras with no rank model; the Cohn algebra is not simple, and this asks whether the Cohn relations alone, without completeness, already force the identity.
  toeplitz-isometry-defects-have-total-rank-at-least-one: that shows completeness never enters the final rank contradiction; this is the open question whether completeness must enter the construction before it.
artifacts:
  - research/artifacts/rank-four-completeness-check-2026-09-12.md
---

**OPEN.** Let `C_2 = <s_0, s_1, t_0, t_1 | t_i s_j = delta_ij>` be the Cohn algebra over `F_2`,
`M` a characteristic-two rank ultraproduct, and `sigma : EL_3(C_2) -> M^x` a homomorphism. Then
`(sigma(x_23(1)) - 1)(sigma(x_12(1)) - 1) = 0`.

**Why it calibrates the gate.** Put `q = 1 - s_0 t_0 - s_1 t_1`, so that
`C_2 / (q) = L_(F_2)(1,2) = R`. Every rank model of `EL_3(R)` pulls back along
`EL_3(C_2) -> EL_3(R)` to a model with the same product `N_23 N_12`.
- **If true,** the identity holds for every characteristic-two rank model of `EL_3(R)`. With
  `el3-unit-root-matrix-units-iff-two-root-identities`,
  `matrix-unit-rank-models-extract-ring-rank-models` and `leavitt-algebra-has-no-unital-rank-model`,
  this gives the binary instance of `leavitt-el3-rank-models-over-finite-fields-are-trivial`.
- **If false,** completeness has to enter any proof of the binary gate. It enters in building the
  corner data, not in the final contradiction, which needs only the three Toeplitz relations of
  `toeplitz-isometry-defects-have-total-rank-at-least-one`.

## Attempts

- **Known structure (w4-r4-complete, 2026-09-12).**
  - `C_2` has no unital homomorphism into a rank ultraproduct: take the toeplitz inequality with
    `e = 1`. So natural models do not exist.
  - `q` is a minimal idempotent: `t_i q = 0 = q s_j`, and `q C_2 q = F_2 q` because the words
    `s_alpha t_beta` span `C_2`. So `g -> 1 + q(g - 1)` embeds `SL_3(F_2)` in `EL_3(C_2)`.
  - The models that are trivial on the kernel of `EL_3(C_2) -> EL_3(R)` are exactly the pulled-back
    models. That kernel contains every `x_ab(r q r')`.
- **Where it stops.** No rank model of `EL_3(C_2)` with `N_23 N_12 != 0` is known. No argument that
  forces the identity from the Cohn relations alone is known either. Models that are nontrivial on
  the kernel are new territory.
- **What this claim is (w4-cohn-el3, 2026-09-12; 013740e0da; artifact
  `research/artifacts/cohn-elementary-group-rank-radical-2026-09-12.md`).**
  - **Tensor squares.** For any unital `S`, the identity holds in every characteristic-two rank model
    of `EL_3(S)` iff every such model is trivial. The tensor square of an identity-satisfying model
    has product `u_23 (x) u_12 + u_12 (x) u_23`, of rank `2 rk(N_12)^2`
    (`two-root-identity-in-all-models-iff-no-nontrivial-model`).
  - **Structure of `G = EL_3(C_2)`** (`cohn-elementary-group-rank-radical-is-trivial-or-everything`).
    - The kernel is `K = GL_fin(W x 3, F_2)`, which is simple with trivial centralizer.
    - The normal subgroups are `1`, `K` and `G`.
    - `C_2` embeds unitally in `L(1,3)` and so in `R`, so `G <= R^x`.
    - The rank radical is `1` or `G`.
  - **So this claim holds iff `EL_3(C_2)` has no injective characteristic-two rank model.** A model
    with kernel `K` is a pullback, and it yields an injective model through `G <= EL_3(R)`. So the
    "new territory" is exactly the faithful models.
  - **Chain.** `binary-jacobson-el3-rank-radical-is-the-finitary-kernel` implies this claim (route
    `cohn-el3-two-root-identity-from-jacobson-rank-radical`), and this claim implies that `R^x` has
    no nontrivial characteristic-two rank model. Neither arrow is known to reverse.
  - **Completeness.** It is load-bearing for the binary gate exactly when `EL_3(C_2)` is
    characteristic-two linear sofic.
