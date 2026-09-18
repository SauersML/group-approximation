---
rg: 2
id: sl-n-q-lacks-property-fw
kind: claim
title: SL_n(Q) and GL_n(Q) lack property FW (and FA) for every n >= 2, although for n >= 3 they are directed unions of Kazhdan subgroups SL_n(Z[1/m])
distinct_from:
  fw-subgroups-of-eventually-similar-groups-virtually-embed: that transfers FW subgroups into vertex groups; this shows SL_n(Q) itself is not an FW input, so that transfer applies only to its finitely generated Kazhdan subgroups.
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: same relation, for Rover--Nekrashevych hosts.
  property-t-implies-property-fa: that is (T) implies FA for countable groups; this is the failure of FA and FW for a countable group that is not finitely generated, together with the (T) of its S-arithmetic subgroups.
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding problem; this closes the abstract-obstruction route of the gq critic's gap G1.
---

**ESTABLISHED** through `sl-n-q-lacks-property-fw-proof`. Not independently
reviewed. Elementary. The tree construction is classical (Serre, *Trees*, Ch. I
§6.1), and no priority is claimed.

## Statement

1. **Every countable group that is not finitely generated lacks FW and FA.**
   There is a `G`-set with a commensurated subset that is not transfixed, namely
   the oriented edges of a tree on which `G` acts without inversions and with
   unbounded orbits.
2. For every `n >= 2`, the groups `SL_n(Q)`, `GL_n(Q)`, `PSL_n(Q)`, `PGL_n(Q)` are
   countable and not finitely generated. So none of them has FW or FA. The same
   holds for `Aff(Q)`, `B_n(Q)`, `U_n(Q)` and `(Q,+)`.
3. **What does hold.** For `n >= 3`,
   `SL_n(Q) = ⋃_m SL_n(Z[1/m!])` is an increasing union of subgroups with
   Kazhdan's property (T), hence with FW. Each `SL_n(Z[1/m])` is an irreducible
   lattice in `SL_n(R) x ∏_{p|m} SL_n(Q_p)`, and each factor has (T) for `n >= 3`.
   These are standard facts; see Bekka--de la Harpe--Valette, *Kazhdan's
   Property (T)*, Ch. 1. The implication (T) ⇒ FW is recorded in
   `fw-subgroups-of-eventually-similar-groups-virtually-embed`.

So FW is not inherited by increasing unions, and `SL_n(Q)` is the standard example.

## What it says about hosts (critic gap G1)

- **The abstract route is dead at its first step, for every `n`.**
  - The planned chain: "SL_n(Q) has FW; it has no proper finite-index subgroups;
    so it lands in one finite product of vertex groups; that contradicts O1".
  - The second step is true: `PSL_n(Q)` is infinite simple and `SL_n(Q)` is
    perfect. The first step is false.
  - So `fw-subgroups-of-eventually-similar-groups-virtually-embed` and
    `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf` cannot be applied to
    `SL_n(Q)` or `GL_n(Q)` themselves. They kill no host class for every
    embedding.
- **Level by level, `n >= 3`.** The lemmas apply to each `SL_n(Z[1/m])`.
  - **Thompson groups of shifts of finite type** (canonical similarities on deep
    cones, including every `V_(d,r)`): clause 2 of the FW lemma makes every FW
    subgroup finite. So none of them contains `SL_n(Z)`, `n >= 3`, and none
    contains `GL_n(Q)` for `n >= 3`. This extends O2 from `V` to that whole class.
  - **Eventually `H`-similar hosts, including Rover--Nekrashevych groups
    `V_d(H)`:** if `GL_n(Q)` embeds, then for every `m` some finite-index
    subgroup of `SL_n(Z[1/m])` embeds in a finite product of vertex groups of
    `H`, respectively in `H^k`. That is a necessary condition on `H`, not a
    contradiction: `SL_n(Z[1/m])` is residually finite and contains no `(Q,+)`.
- **What would restore the kill (open).** Take an embedding into an eventually
  `H`-similar host. The FW lemma gives, for each `m`, a commensurated subset for
  `SL_n(Z[1/m!])` together with a transfixing set.
  - Suppose the transfixing defects could be bounded independently of `m`.
  - Then `sup_g |gM Δ M| < ∞` over all of `SL_n(Q)`. A commensurated subset with
    bounded defect is transfixed (Brailovsky--Pasechnik--Praeger). So `SL_n(Q)`
    would itself land in a finite product of vertex groups, contradicting O1 when
    those groups are residually finite.
  - In the coset-tree action of the proof the defects grow like the level. The
    open question is whether a *host's* commensurated subsets must have bounded
    defect on the `SL_n(Z[1/m!])`.
