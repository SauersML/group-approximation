---
rg: 2
id: adjoint-image-is-stable-under-klein-doubling
kind: claim
title: Conjugating by the one-level amplification maps the ternary adjoint image into its Klein corner
distinct_from:
  klein-level-one-splitting-is-outside-adjoint-image: that shows the amplification delta and compression Psi are not in the adjoint image; this shows delta T Psi is, for every T in it.
  klein-corner-contains-unital-copy-of-projective-group-algebra: that is the group algebra embedding x -> delta_*(x) e_K; this is its image-level form and the intertwining identities behind it.
artifacts:
  - research/artifacts/klein-target-balanced-invariant-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

With `k`, `R`, `PG`, `K`, `e_K`, `delta_*` as in `klein-corner-contains-unital-copy-of-projective-group-algebra`,
`rho : k[PG] -> R (x) R^op` the adjoint evaluation, and the tensors `delta = sum s_i (x) t_i^op`,
`Psi = 2 sum t_i (x) s_i^op`:

    delta rho(x) = rho(delta_*(x)) delta,    Psi rho(delta_*(x)) = rho(x) Psi,    delta rho(x) Psi = rho(delta_*(x) e_K).

So `Theta(T) = delta T Psi` is an injective algebra endomorphism of `A = rho(k[PG])` with
`Theta(1) = rho(e_K)`. Consequence: `delta^2 in A` iff `Psi^2 in A` iff `Psi^2` has a right inverse in
`A`, via the flip antipode `sigma(rho(g)) = rho(g^-1)`. Proposition 8 and Corollary 9 of the artifact.
