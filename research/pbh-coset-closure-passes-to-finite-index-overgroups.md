---
rg: 2
id: pbh-coset-closure-passes-to-finite-index-overgroups
kind: claim
title: The coset conditions of the permutational class pass from a finite-index subgroup to the whole group, so every virtual retract gives coset lamplighters and identity-edge HNN extensions in B_A
distinct_from:
  pbh-coset-wreaths-iff-identity-edge-hnns: that proves the equivalence of the coset conditions (a)-(e) for one pair (G, C); this shows the conditions for (G, C) follow from the conditions for (H, C) with H of finite index in G.
  free-group-coset-wreaths-satisfy-pbh: that proves the conditions from a normal finite-index N with N ∩ C a retract of N and notes that plain virtual retracts are not enough for its argument; this removes the normality requirement, so plain virtual retracts suffice.
  pbh-closed-under-decidable-permutational-wreaths: that is the open closure for all decidable stabilizers; this settles it for every stabilizer that is a virtual retract.
requires:
  - pbh-coset-wreaths-iff-identity-edge-hnns
  - boone-higman-type-a-class-closed-under-finite-extensions
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no priority claimed).

## Statement

Let `G ∈ B_A`, and let `C ≤ H ≤ G` with `[G : H] < ∞`. Suppose the pair `(H, C)`
satisfies the equivalent conditions (a)–(e) of `pbh-coset-wreaths-iff-identity-edge-hnns`,
e.g. `Z/2 ≀_{H/C} H ∈ B_A`. Then so does the pair `(G, C)`. In particular, for all
`A, K ∈ B_A`:
- `A ≀_{G/C} G ∈ B_A`;
- `G *_C (C × K) ∈ B_A`, including the identity-edge HNN extension `⟨G, t | [t, c] = 1 (c ∈ C)⟩`.

**Corollary (virtual retracts).** If `C` is a retract of some finite-index `H ≤ G`, the
pair `(G, C)` satisfies (a)–(e). Indeed `(H, C)` satisfies (e) by case 3 of that node, and
`H ∈ B_A` as a subgroup of `G`.

## Proof

1. **Imprimitive embedding.** Let `t_1, …, t_m` be a left transversal of `H`, with
   `g t_i = t_{σ_g(i)} h_i(g)` and `h_i(g) ∈ H`. Then `G/C = ⊔_i t_i (H/C)`. The map
   - `g ↦ (h(g), g)`, where `h(g)` has `h_i(g)` in coordinate `σ_g(i)`,
   - the lamp at `t_i hC` sent to the lamp at `hC` in coordinate `i`,

   defines an injective homomorphism `A ≀_{G/C} G -> (A ≀_{H/C} H) ≀_{G/H} G`. This is the
   Kaloujnine–Krasner cocycle map with top group `G` acting on `G/H` through `σ`. It
   respects the action on lamps because `g t_i hC = t_{σ_g(i)} h_i(g) hC`.
2. **Finite top sets.** For a finite `G`-set `Y` and any `L`, the map `(f, g) ↦ ((f, σ_g), g)`
   embeds `L ≀_Y G` in `(L ≀ Sym(Y)) × G`, where `L ≀ Sym(Y)` is the finite-index
   overgroup `L^Y ⋊ Sym(Y)` of `L^Y`.
3. **Closure.** Take `L = A ≀_{H/C} H`, which is in `B_A` by (b) for `(H, C)`. Then `L^m`,
   `L ≀ Sym(G/H)` and `(L ≀ Sym(G/H)) × G` are in `B_A`, by closure under finite direct
   products and finite-index overgroups (`boone-higman-type-a-class-closed-under-finite-extensions`).
   So `A ≀_{G/C} G ∈ B_A` by steps 1–2 and closure under subgroups. This is (b) for
   `(G, C)`, and the equivalence gives (a)–(e). ∎

## Applications

These hold wherever the top group is in `B_A` and the subgroup is a virtual retract.
- **Free groups:** every f.g. subgroup, via M. Hall's theorem. This reproves
  `free-group-coset-wreaths-satisfy-pbh` without the normal-subgroup step.
- **Virtually abelian groups:** every subgroup of a f.g. virtually abelian group
  (elementary: `C ∩ Z^n` has finite index in a direct summand of `Z^n`).
- **Cited, not re-read at source; stated conditionally on the cited theorem.**
  - Quasiconvex subgroups of virtually compact special hyperbolic groups (Haglund–Wise).
  - F.g. subgroups of limit groups (Wilton, *Hall's theorem for limit groups*).
  - F.g. subgroups of surface groups (Scott).

  These top groups are in `B_A` by `permutational-boone-higman-iff-full-cantor-hosts` (via
  RAAGs in `2V`). So `A ≀_{G/C} G` and `G *_C (C × K)` embed in finitely presented simple
  groups for all such `(G, C)` and all f.g. `A, K ∈ B_A`.

## Lesson for general BH

- **Coset-type permanence is a finite-index property of the pair `(G, C)`.** Wreaths over
  `G/C`, identity-edge HNN extensions over `C`, and realizing `C` as a centralizer all hold
  for `(G, C)` as soon as they hold inside one finite-index subgroup containing `C`. So every
  virtual-retraction theorem in geometric group theory transfers wholesale into Boone–Higman
  permanence.
- **The limit of this mechanism.** Virtual retracts of residually finite groups are
  profinitely closed. So this mechanism reaches only closed stabilizers, the same boundary
  as every residually finite host (`abelian-lamp-wreaths-are-rf-iff-stabilizers-are-closed`).
- **The dense case needs another tool.** Decidable but profinitely dense stabilizers, such
  as `PSL_2(Z) ≤ PSL_2(Z[1/n])`, need the Cantor-host mechanism
  (`wreaths-over-clopen-stabilizer-cosets-lie-in-b-a`).
- **Where the open closure now sits.** The general
  `pbh-closed-under-decidable-permutational-wreaths` has these two complementary tools. The
  remaining cases are decidable stabilizers that are neither virtual retracts nor
  commensurated-above clopen stabilizers in some full host.
