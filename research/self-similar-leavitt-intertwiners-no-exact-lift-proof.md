---
rg: 2
id: self-similar-leavitt-intertwiners-no-exact-lift-proof
kind: route
title: Equivariance forces finite twisted-conjugation orbits, and a group without finite-index subgroups makes the endomorphism inner
target: self-similar-leavitt-intertwiners-have-no-exact-lift
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
  - odd-leavitt-unit-groups-mod-scalars-are-fp-simple
artifacts:
  - research/artifacts/leavitt-self-similarity-exactness-2026-09-12.md
---

Section 1 of the artifact.

1. **No finite-index subgroups.** Perfectness of `G` and simplicity of `G/F_p^x` show that `G`
   has no proper subgroup of finite index (Lemma 1.1). The normal core of a finite-index subgroup
   maps onto the simple quotient, so its quotient is abelian of order at most `p - 1`, and
   perfectness kills that quotient.
2. **Invariance.** Comparing coefficients in `V[g] = [phi(g)]V` gives `v(y) = v(phi(g)^-1 y g)`.
   So `v` is invariant under the action `g . y = phi(g) y g^-1`. The right-hand version uses
   `g . y = g y phi(g)^-1`.
3. **Contradiction.** A nonzero finitely supported invariant `v` has a finite orbit. Its stabilizer
   has finite index, so it is `G`. Then `phi = Ad(y)` is onto, contradicting the hypothesis.
