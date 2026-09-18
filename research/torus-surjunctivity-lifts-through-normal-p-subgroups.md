---
rg: 2
id: torus-surjunctivity-lifts-through-normal-p-subgroups
kind: claim
title: An injective torus automaton is onto as soon as its restriction to the fixed torus of a locally normal p-subgroup is onto, so torus surjunctivity passes from G/N to G
distinct_from:
  torus-automata-over-rf-or-domain-groups-are-surjunctive: that restricts to fixed tori of finite-index normal subgroups and uses invariance of domain on finite tori; this restricts to fixed tori of infinite-index normal subgroups, which are full shifts over the quotient, and imports surjectivity there.
  torus-degree-regular-on-prime-power-residual-support: that lifts only the augmentation, from the circle of constants, through a p-group quotient of the support group; this lifts invertibility of the whole image degree p_N(D) through a normal p-subgroup of the ambient group, and so defeats the Bezout witnesses that stop augmentation-only proofs.
artifacts:
  - research/artifacts/torus-normal-p-lifting-2026-09-17.md
  - experiments/torus-normal-p-lifting-2026-09-17/check_normal_p_lifting.py
---

Let `tau` be an injective continuous `G`-equivariant self-map of `(T^d)^G`, with degree
matrix `D in M_d(Z[G])`. Call `N <| G` a **locally normal `p`-subgroup** if every finite
subset of `N` lies in a finite `p`-subgroup of `N` that is normal in `G`.

**Claim.**
- (a) **Restriction.** For every normal `N <| G`, of any index, `tau` maps
  `Fix(N) = (T^d)^(G/N)` into itself, and the restriction `tau_N` is an injective torus
  automaton over `G/N` with degree `p_N(D)`.
- (b) **Lifting.** If `N` is a locally normal `p`-subgroup and `p_N(D) in GL_d(Z[G/N])`,
  then `D mod p` is invertible in `M_d(F_p[G])`, so `xi -> xi D` is injective on `Q[G]^d`.
- (c) **Extension closure.** If `N` is a locally normal `p`-subgroup and `tau_N` is onto,
  then `tau` is onto. Hence if `G/N` is torus-surjunctive at `d`, so is `G`. The same holds
  along any finite chain of such subgroups, and for every finite solvable normal subgroup
  `L` (if `G/L` is torus-surjunctive at `d`, so is `G`).

Read backwards, (c) says a counterexample to `injective-torus-automata-have-regular-degree`
descends to `G/N`. Minimal counterexample hosts have no nontrivial locally normal
`p`-subgroup and no nontrivial finite solvable normal subgroup.

**ESTABLISHED 2026-09-17** by [[torus-surjunctivity-lifts-through-normal-p-subgroups-proof]].
