---
rg: 2
id: mod-s2-finite-image-near-scalar-reps-are-torelli-abelian
kind: claim
title: A finite-image representation of Mod(S_2) that puts a separating twist within 1/2 of a root-of-unity scalar has abelian Torelli image, in every dimension
distinct_from:
  mod-s2-torelli-abelian-scalars-are-shifted-maslov-multipliers: that is a dictionary for representations already known to be Torelli-abelian; this proves that the finite-image near-scalar ones always are.
  mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors: that bounds finite-image models level by level with a floor that degrades with the level; this is a dimension-free and level-free structural fact about the same representations.
  deligne-torelli-character-counts-separating-twists: its (ST5) excludes exact cube-root scalars; this says what near-scalar finite-image representations look like, namely that the Torelli group acts through commuting unitaries.
---

**ESTABLISHED** through `mod-s2-finite-image-near-scalar-torelli-abelian-proof`. Unreviewed; no novelty
claimed (the lemma used is the Frobenius commutator lemma from the proof of Jordan's theorem, reproved in
the route).

**Statement.** Let `M = Mod(S_2)`, `K` the Torelli group, `t_s` a separating twist, and `lambda` a root of
unity. If `rho : M -> U(d)` has finite image and

```text
|| rho(t_s) - lambda I ||_op  <  1/2 ,
```

then `rho(K)` is abelian, so `rho` factors through `G = M/[K,K]`. The constant `1/2` does not depend on
`d`, `rho` or `lambda`.

**Consequences.**
- For `lambda = omega^(+-1)`: every finite-image `rho` with `||rho(t_s) - omega^(+-1) I|| < 1/2` falls under
  the dictionary `mod-s2-torelli-abelian-scalars-are-shifted-maslov-multipliers`. So the finite-image part of
  `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap` is exactly the finite-image part of
  `sp4-shifted-maslov-multipliers-stay-far-on-finite-index`. In that part the character `chi` has finite
  order (so `h` is rational) and the projective representation `u` has finite image.
- For `lambda = 1`: honest finite-image representations with `rho(t_s)` within `1/2` of `I` are Torelli-abelian
  too. This applies to any such representations produced by pulling back Sp4 windings, as in the
  swarm-0917 bus lemma `mod-s2-stability-forces-honest-torelli-windings` (not in this worktree), whenever they have
  finite image. Their winding `Tr log rho(t_s) / 2 pi i` equals `sum_chi (dim W_chi) h_chi(s)`, summed over the
  Torelli eigencharacters, with `h_chi` as in Step 2 of `mod-s2-torelli-abelian-scalars-shifted-multipliers-proof`.
- What remains for the gap is representations with infinite image, where the commutator iteration below
  converges to the identity without reaching it.
