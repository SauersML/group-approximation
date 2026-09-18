---
rg: 2
id: mod-s2-near-scalar-reps-reduce-to-torelli-abelian
kind: claim
title: If honest representations of Mod(S_2) put a separating twist arbitrarily near a cube-root scalar, then Torelli-abelian ones do too
distinct_from:
  mod-s2-finite-image-near-scalar-reps-are-torelli-abelian: that proves the reduction for finite-image representations with no loss; this asks for it for all honest representations, where the commutator iteration no longer terminates.
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that is the gap itself; this is only the reduction of the gap to its Torelli-abelian part.
  mod-s2-torelli-abelian-scalars-are-shifted-maslov-multipliers: that describes the Torelli-abelian class exactly; this asks that the class suffices.
---

**OPEN.** With `Z_hon` as in `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap` and `Z_ab` as in
`mod-s2-torelli-abelian-scalars-are-shifted-maslov-multipliers`:

```text
1/3 in Z_hon   implies   1/3 in Z_ab .
```

That is: if for every `epsilon` some honest `rho` has `||rho(t_s) - omega I|| < epsilon`, then for every `epsilon`
some honest `rho` with `rho(K)` abelian does.

## Known

- **Finite image: done.** A finite-image `rho` with `||rho(t_s) - omega I|| < 1/2` is already Torelli-abelian, by
  `mod-s2-finite-image-near-scalar-reps-are-torelli-abelian`. So only infinite-image `rho` can separate
  `Z_hon` from `Z_ab` at `1/3`.
## Attempts

- **2026-09-18, swarm-0917-w10-w10-deligne-pull: the Frobenius iteration, and where it stops on infinite image.**
  For infinite-image `rho`, Lemma 1 of
  `mod-s2-finite-image-near-scalar-torelli-abelian-proof` still makes the iterated commutators
  `[g,[g,...,h]]` of the unitaries `omega^-1 rho(t_x)` converge to `I` geometrically. But without a minimal
  distance they need not reach `I`. So `rho(K)` is only "Zassenhaus-small", not abelian.
  - The closure `L` of `rho(M) . <omega>` is a compact Lie group. The elements `omega^-1 rho(t_x)` lie in a
    fixed-radius, dimension-free neighbourhood of `I`. The subgroup they generate is dense in a connected
    subgroup of `L`, which may be non-abelian.
  - A reduction would have to replace `rho` by a representation of `G = M/[K,K]` with no worse operator-norm
    distance. Two natural candidates are passing to the associated graded of the lower central series of
    `rho(K)`, or specializing a Galois conjugate with finite image. Neither is checked.
