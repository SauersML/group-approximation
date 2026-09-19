---
rg: 2
id: negative-euler-inputs-get-infinitely-generated-tree-stabilizers
kind: claim
title: Every group in BS_{F_2} or BS_Z has Euler characteristic at least zero, so a torsion-free non-free input with negative Euler characteristic meets every vertex stabilizer of a locally finite virtually-free-stabilizer tree host in an infinitely generated subgroup
distinct_from:
  gersten-pairs-lie-in-no-locally-finite-tree-host: that excludes tree hosts altogether for inputs containing a Gersten pair; this excludes nothing outright and applies to free-base HNN extensions, which contain no Gersten pair, forcing instead infinitely generated stabilizers through the Euler characteristic.
  profinite-tree-hosts-make-fa-subgroups-residually-finite: that uses FA subgroups and the finite residual; free-base HNN extensions have no nontrivial FA subgroups, and this uses the rational Euler characteristic of the restricted action.
  domain-exact-hnn-hosts-have-multivalley-kernels: that describes the kernel of one Hall-host map; this constrains every injective map into any free-stabilizer locally finite tree host, whatever its construction.
  commensurated-cat0-witnesses-force-finite-rational-cd: that bounds the rational cohomological dimension of quotients F/N cut out by compact open subgroups; this is about subgroups G of tree hosts and their Euler characteristic, not about quotients.
  free-generalized-bs-groups-have-type-a-overgroups: that gives type (A) overgroups to every member of BS_{F_2}; this shows which inputs can never be members, namely those with negative Euler characteristic.
---

**ESTABLISHED.** The proof is `negative-euler-tree-stabilizers-proof`.
It uses only Bass--Serre theory and the multiplicativity of the rational Euler characteristic.

## Statement

1. **Sign of `χ` on the BLIW classes.** Let `G` be the fundamental group of a finite graph of
   groups whose vertex groups are finitely generated free groups and whose edge inclusions all have
   finite index. Suppose the graph of groups is reduced to the minimal subtree, meaning `G` fixes no
   vertex of the Bass--Serre tree `T` and `T` is `G`-minimal. Then

   ```text
   χ(G) = Σ_[v] χ(G_v) (1 - deg(v)/2) >= 0 .
   ```

   The sum runs over vertex orbits, and `deg(v)` is the valence of `v` in `T`. Equality holds iff
   every vertex group is cyclic or `T` is a line. In particular every member of `BS_{F_2}` and
   `BS_Z` (as defined in `bliw-locally-finite-tree-actions-embed-in-fp-simple-groups`) that is not
   itself free has `χ >= 0`.
2. **Host restriction.** Let `H` act on a locally finite tree `X` with every vertex stabilizer
   virtually free, of any rank. Let `G <= H` be finitely generated, torsion-free and not free, with
   a finite `K(G,1)`. If `G ∩ H_x` is finitely generated for one vertex `x`, then it is finitely
   generated for all `x`, and `G` is a group as in item 1. Hence `χ(G) >= 0`.
3. **The kill.** If `χ(G) < 0`, then `G ∩ H_x` is infinitely generated for every vertex `x` of
   every such host `X`. For `G = F *_{φ : A -> B}` with `F` free of rank `r` and `A` free of rank
   `a`, `χ(G) = a - r`. So this applies to every non-free HNN extension of a free group whose
   edge has smaller rank than the base. Examples are surface groups written as `F_{2g-1} *_Z`.
   Non-freeness must be assumed: `< x, y, t | t x t^-1 = y >` is free, with `χ = -1`.
4. **The zero case.** If `χ(G) = 0` and the stabilizers `G ∩ H_x` are finitely generated and
   non-cyclic, then `G` acts on a line with finitely generated free vertex stabilizers. So `G` is
   (f.g. free)-by-`Z` or (f.g. free)-by-`D_∞`.

## What it kills

This applies to the Hall hosts of Attempt bh-free-05 on `bh-embeddability-survives-decidable-edge-hnn`
(`H = Y *_Φ`, `Y = F * <b>`, vertex stabilizers conjugates of `Y`), and to every other torsion-free
host in `BS_{F_2}`.

- **Invariant:** the rational Euler characteristic of the input.
- **Where every member dies:** at the restriction of the host's tree action to the input's minimal
  subtree.
- **What dies:** any injectivity proof that exhibits `G ∩ Y` as a finitely generated subgroup,
  including every terminating Stallings folding sequence for `<F, t^-1 B̄ t, ...>` inside `Y`. Such
  a proof certifies only inputs with `χ >= 0`, and when stabilizers are f.g., only inputs that are
  already in `BS_{F_2}` or `BS_Z`. Since the input contains the base `F` of rank at least 2, it
  lies in `BS_{F_2}`, where BLIW §12.5 applies directly and the host is unnecessary.
- **What survives:** hosts in which `G ∩ Y` is infinitely generated. The genus-2 surface group
  `π_1 Σ_2` (`χ = -2`) is the calibration. The kernel of any surjection `π_1 Σ_2 -> Z` is an
  infinitely generated free group, and the resulting action on a line is an action on a locally
  finite tree with free stabilizers. So nothing here stops `π_1 Σ_2` from acting on such a tree, and
  item 3 correctly predicts that every such action has infinitely generated stabilizers.

## What it does not do

- It does not refute `bh-embeddability-survives-decidable-edge-hnn`.
- It does not rule out Hall hosts for inputs with `χ < 0`. It says only that their injectivity
  cannot be witnessed by a finitely generated stabilizer.
- Inputs with `χ(G) >= 0` are untouched. These include the large-type triangle Artin reduction
  `F_3 *_{F_7}`, with `χ = 4`, and every one-sided (finite-index domain) HNN extension of a free
  group.
