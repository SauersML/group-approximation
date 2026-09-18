---
rg: 2
id: fp-groups-with-a-locally-moving-simple-subgroup-are-isolated
kind: claim
title: A finitely presented group acting faithfully with a simple subgroup whose rigid stabilizers are nonabelian, or containing the finitary alternating group, is isolated
distinct_from:
  fp-simple-groups-are-isolated: that is the case where the whole group is simple; this allows an arbitrary finitely presented overgroup of a locally moving simple subgroup, which need not be simple (for example Thompson's F, or Houghton's H_3).
  outer-extensions-of-fp-simple-groups-are-isolated: that needs a finitely presented simple normal subgroup with trivial centralizer; here the simple subgroup T need not be normal, finitely generated or finitely presented, and the monolith ncl(T) is produced by the argument rather than assumed.
  every-decidable-group-embeds-in-an-isolated-group: that is the open universality question; this is a sufficient condition for a given group to be isolated.
  lampshuffler-groups-are-not-fp2-over-q: that kills one family of candidate hosts of the finitary kind by finiteness; this is the normal-structure half, showing such hosts would be isolated if finitely presented.
---

**ESTABLISHED** by `locally-moving-simple-subgroup-commutator-proof` (elementary hand
proof, the standard double-commutator trick; not independently reviewed). No novelty
claimed for the method. Whether Cornulier--Guyot--Pitsch list these examples was not
checked.

Terms as in `fp-simple-groups-are-isolated` (CGP arXiv:math/0511714). *Finitely
discriminable*: some finite `F ⊂ Γ − {1}` meets every nontrivial normal subgroup.
*Isolated* iff finitely presentable and finitely discriminable (CGP, lines 554–557).

## Statement

Let `Γ` act faithfully on a set `X`, and let `T ≤ Γ`. Assume one of the following.

- **(top)** `X` is a Hausdorff space, `Γ` acts by homeomorphisms, `T` is simple, and
  for every nonempty open `U ⊆ X` the rigid stabilizer
  `T_U = {t ∈ T : t fixes X − U pointwise}` is nonabelian.
- **(fin)** `|X| ≥ 5` and `T = Alt_fin(X)`, the finitely supported even permutations of
  `X`, is contained in `Γ`.

Then:
1. every nontrivial subgroup `N ≤ Γ` normalized by `T` contains `T`;
2. `C_Γ(T) = 1`;
3. `M = ncl_Γ(T)` is simple, lies in every nontrivial normal subgroup of `Γ` (so `Γ` is
   monolithic with monolith `M`), and `C_Γ(M) = 1`, so `Γ ≤ Aut(M)`;
4. `Γ` is finitely discriminable, with `F = {t}` for any `t ∈ T − {1}`;
5. if `Γ` is finitely presented, `Γ` is isolated.

No finiteness is assumed of `Γ` in items 1–4.

## Examples

- Any finitely presented `Γ ≤ Homeo(C)` containing Thompson's `V` in its standard action
  on the Cantor set `C`. `V` is simple, and for open `U ⊇ [w]` the elements of `V`
  supported in the cone `[w]` form a copy of `V`, so (top) holds. So `V`, Röver's group,
  and every finitely presented Nekrashevych group `V_G` are isolated.
- Thompson's `F` on `[0,1]` with `T = F'` (simple; supported copies of `F` in every open
  interval) and `T` on the circle. These are standard facts, not re-cited.
- Houghton's `H_n`, `n ≥ 3`, under (fin): they contain `FSym(Ω_n)` and are finitely
  presented (Brown, JPAA 44 (1987), as recorded in `lampshuffler-groups-are-not-fp2-over-q`).
  So they are isolated.

## Consequence

This gives the host class behind `decidable-groups-embed-in-fp-locally-moving-groups` and
the route `isolated-overgroup-via-locally-moving-hosts`. The only missing input for an
isolated overgroup is finite presentation; no simplicity of `Γ` and no finite
presentation of the monolith is needed.

DERIVATION
locally-moving-simple-subgroup-commutator-proof
