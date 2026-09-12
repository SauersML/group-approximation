---
rg: 2
id: self-similar-leavitt-intertwiners-have-no-exact-lift
kind: claim
title: No nonzero group-algebra element intertwines the Leavitt unit group with a proper self-embedding
distinct_from:
  leavitt-matrix-amplification-in-unit-group-algebra: that embeds matrix algebras over the binary group algebra into its corners using the self-similar endomorphism; this proves that the self-similar endomorphisms themselves have no nonzero finitely supported equivariant elements, so the Leavitt isometries have no exact equivariant lift.
artifacts:
  - research/artifacts/leavitt-self-similarity-exactness-2026-09-12.md
---

Let `p` be a prime, `R = L_(F_p)(1,2)`, `G = R^x`, `k` any field, and `phi : G -> G` an injective
homomorphism that is not surjective. If `V` in `k[G]` satisfies

    V [g] = [phi(g)] V   for all g,        or        [g] V = V [phi(g)]   for all g,

then `V = 0`.

This covers the two self-similar endomorphisms `delta(g) = s0 g t0 + s1 g t1` and
`iota(g) = s0 g t0 + s1 t1`, neither of which is onto. At the level of `R`, the Leavitt isometries
are equivariant: `s_i r = delta(r) s_i`, `r t_i = t_i delta(r)`, `s0 g = iota(g) s0` and
`g t0 = t0 iota(g)`. So none of `s0, s1, t0, t1` has an exact equivariant lift to `k[G]`. For odd
`p` the same holds inside the anti-central summand `eps_- k[G]`.

*Proof idea.*
- Equivariance makes the coefficient function invariant under the twisted conjugation action
  `g . y = phi(g) y g^-1`.
- Finite support forces a finite orbit, hence a stabilizer of finite index.
- `G` is perfect and simple modulo its finite centre, so it has no proper finite-index subgroup.
- The stabilizer is then all of `G`, and `phi` is inner, which contradicts non-surjectivity.

Full proof: Section 1 of the artifact.

**Why it matters for the ternary corner.** Amplification by `delta` lifts the Leavitt isomorphism
`Theta : M_2(R) -> R` but carries every lift defect injectively. An exact Cohn family in `S_-` must
therefore break `delta`-equivariance, and it must leave the locally finite dyadic constant subgroup
where every amplification matrix unit lives. Section 2 of the artifact.
