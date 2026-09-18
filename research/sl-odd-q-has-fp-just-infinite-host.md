---
rg: 2
id: sl-odd-q-has-fp-just-infinite-host
kind: claim
title: For infinitely many odd m, SL_m(Q) maps nontrivially to a finitely presented group that is just-infinite above its image
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that asks for an embedding in a finitely presented simple group; this asks only for a nontrivial homomorphism into a finitely presented host with a normal-subgroup dichotomy above the image, and is equivalent to it by the routes gl-n-q-root-via-just-infinite-hosts and sl-odd-q-just-infinite-host-from-root.
  gl-n-q-in-permutational-boone-higman-class: that relaxes the host to the type (A) class; this relaxes it to just-infinite-above-the-image hosts, a different host family.
  sl-odd-q-simple-inputs-for-gl-n-q-root: that is the elementary reduction to simple inputs; this is the open host problem for those inputs.
---

**OPEN.** For infinitely many odd `m >= 3` there are a finitely presented group
`Γ_m` and a nontrivial homomorphism `ρ_m : SL_m(Q) -> Γ_m` such that every
nontrivial normal subgroup of `Γ_m` inside `<<ρ_m(SL_m(Q))>>` has finite index in
`Γ_m`. For example, `Γ_m` just-infinite.

**Equivalent to the root** `gl-n-q-embeds-in-fp-simple-group`:
- route `gl-n-q-root-via-just-infinite-hosts` proves the root from this;
- route `sl-odd-q-just-infinite-host-from-root` proves this from the root.

For one fixed `n`, a single odd `m >= n + 1` suffices for `GL_n(Q)`.

**What it relaxes.**
- The map need only be nontrivial, because `SL_m(Q)` is simple.
- The host may have finite quotients. Only normal subgroups under the image
  matter.
- Normal-subgroup theorems are the usual source of such hosts, but see the
  calibration below.

**Calibration: two tests every candidate host must pass.**
1. **Not residually finite.** The host contains an infinite simple subgroup. So
   finitely generated linear groups are excluded, including all lattices in
   linear algebraic groups over local fields (Mal'cev).
2. **Contains a non-finitely-generated abelian group.** `(Q,+) <= SL_m(Q)`, so the
   host contains `Q`. A group acting properly and cocompactly by isometries on a
   CAT(0) space has only finitely generated abelian subgroups (Bridson–Haefliger,
   *Metric Spaces of Non-Positive Curvature*, Ch. II.7, the Solvable Subgroup
   Theorem and its corollaries). So cocompact CAT(0) lattices are excluded,
   including every Burger–Mozes lattice in a product of trees, even the simple
   ones.

Neither test excludes non-uniform lattices, or lattices in non-linear Lie
groups (for example Deligne's non-residually-finite lattices,
`deligne-lattice-satisfies-boone-higman`). Nor does either test exclude hosts
built from V-type or germ constructions. Other swarm nodes record further host
exclusions: V and VA, and anything without distorted cyclic subgroups (root
node, O2–O4).

## Attempts

None yet.
