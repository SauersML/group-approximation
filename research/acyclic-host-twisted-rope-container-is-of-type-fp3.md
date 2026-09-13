---
rg: 2
id: acyclic-host-twisted-rope-container-is-of-type-fp3
kind: claim
title: "Some acyclic-host twisted rope container of a universal finitely presented group is of type FP_3"
distinct_from:
  twisted-rope-trick-container-is-not-fp3-over-fp2-hosts: that proves the twisted container fails over hosts with finite rational H_2 and whenever the two embeddings agree on H_2; this is the case it leaves open, a host with infinite rational H_2 on which the embeddings differ injectively
  universal-fp-group-embeds-in-an-rp-fp3-group: that only asks for some recursively presented FP_3 host of a universal group; this names one explicit finitely presented candidate host
artifacts:
  - research/artifacts/zp-z1-01-ffz-fp3-level-three-2026-09-13-part2.md
---

**Construction.**
- Let `G = F/R` be a finitely presented, integrally acyclic group containing a
  universal finitely presented group. It exists by Baumslag–Dyer–Miller,
  Topology 22 (1983), which embeds every recursively presented group in a
  finitely presented acyclic group.
- Let `L = F_1 *_R F_2` be the double and `π: L → G` the map killing `F_2`.
- Let `ι_0: L → P_0` embed `L` in a finitely presented acyclic group (BDM
  again; `L` is recursively presented).
- Let `K_ac(G)` be the HNN extension of `A = P_0 × L × G` along `L`
  conjugating `f_1(y) = (ι_0(y), 1, 1)` to `f_2(y) = (1, y, π(y))`.

This is the twisted rope-trick container of
`twisted-rope-trick-embeds-g-in-a-finitely-presented-group` over the host
`P = P_0 × L`, with `ι = (ι_0, 1)` and `ι' = (1, id)`.

**Claim.** For some such choice of `G`, `P_0` and `ι_0`, the group `K_ac(G)`
is of type `FP_3`. Since it is finitely presented, it would then be of type
`F_3` (Lemma 2.1 of Fournier-Facio–Zaremsky arXiv:2607.21727v1). It contains
every finitely presented group, so this would prove
`every-finitely-presented-group-embeds-in-an-f3-group`.

**Proved so far (derivations in the artifact; unreviewed).**

1. `K_ac(G)` is finitely presented, although its vertex group is not. The
   infinitely many relations `r^(1) = r^(2)` of the `L` factor follow from the
   finite relations of `P_0` and `G`, the commutation relations between
   generators, and the conjugation relations for the generators of `L`.
2. `K_ac(G)` contains `G`.
3. `K_ac(G)` is an integral homology circle: `H_1 = Z` and `H_k = 0` for
   `k ≥ 2`. In the HNN Mayer–Vietoris sequence each `α_k` (`k ≥ 1`) is `−` an
   isomorphism, because `H_*(A) ≅ H_*(L)`, `f_1` is homologically trivial and
   `f_2` induces the identity. So none of the trivial-coefficient
   obstructions (Theorem B, `fp2-vertex-graph-of-groups-infinite-h2-edge-kills-fp3`,
   `twisted-rope-trick-container-is-not-fp3-over-fp2-hosts`) applies, in any
   degree.

## Attempts

- **Reformulation by products of free modules (open).** By the Bieri–Eckmann
  direct-product criterion, still to be quoted from Bieri's notes before use,
  a finitely presented group is of type `FP_3` iff `H_2(-; Π_I ZK) = 0` for all
  `I`. With `W = Π_I ZK`, Mayer–Vietoris makes this equivalent to two
  conditions:
  - `H_1(f_2; W): H_1(L; W) → H_1(A; W)` is injective. The `f_1` term
    vanishes because `P_0` is finitely presented.
  - `H_2(f_1; W) − H_2(f_2; W): H_2(L; W) → H_2(A; W)` is surjective.
- **Injectivity at level 1: unresolved.** The retraction `A → L` inverts
  `f_2` only after collapsing the `L`-cosets inside each `A`-coset. Classes
  supported on differences across those cosets are not controlled.
- **Surjectivity at level 2: doubtful.** `H_2(A; W)` carries the level-2
  product defects of `P_0` and `G` when they are not of type `FP_3`. `f_2`
  reaches `G` only through `π` from a group of cohomological dimension 2,
  which has no identities among relations to cover them.
- **Choosing `P_0` of type `FP_3` removes the `P_0` defect but may be
  circular.** An `FP_3` host of `L` is not known to be easier to find than one
  of a universal group.
- **Related variant reported to fail.** Lane z1-01-embed-pos found that an
  acyclic `FP_∞` host with an `FP_∞`-kernel edge fails on product coefficients
  because `ι × 1` factors through the host. Here the host contains `L` as a
  factor and `ι'` lands there, so that computation does not transfer directly.
