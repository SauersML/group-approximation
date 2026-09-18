---
rg: 2
id: open-euclidean-artin-types-resist-garside-normal-form-routes
kind: claim
title: The Euclidean Artin types still open for B_A (D̃_n, Ẽ_6, Ẽ_7, Ẽ_8, F̃_4) are complete atoms, have no fiber-type toric model, and embed only in infinite-type Garside groups, so none of the current routes applies as stated
distinct_from:
  euclidean-artin-toric-commensurability: that reduces each Euclidean type to its toric Weyl arrangement group and records the non-fiber-type obstruction; this adds the Garside and automatic-structure side, and the combinatorial side, and fixes the open list.
  complete-artin-atoms-are-invisible-to-artin-combinatorics: that is the general statement for complete Artin groups; this applies it to the open Euclidean types.
  rational-germ-singular-sets-are-finite-graph-path-spaces: that makes the germ-extension tests decidable for a rational action on a normal-form boundary of an automatic group; this records that no such normal form is available here from McCammond--Sulway.
  d-tilde-artin-groups-satisfy-permutational-boone-higman: that is the open D̃_n node with its own reductions; this lists D̃_n among the others.
---

**ESTABLISHED** as a status and obstruction record (lane bh-artin, 2026-09-18; the mathematical content is elementary or cited, not independently reviewed). It settles no case.

## The open list

On main, the Euclidean Artin groups in `B_A` are:
- **Ã_n**: BFFHZ Corollary B (`aut-free-groups-satisfy-permutational-boone-higman`);
- **B̃_n**, `n >= 3`: `b-tilde-artin-groups-satisfy-permutational-boone-higman`;
- **C̃_n**: `c-tilde-artin-groups-satisfy-permutational-boone-higman`;
- the triangles **Ã_2, C̃_2, G̃_2**: BLIW Corollary 12.8 with Remark 12.7, as recorded in `artin-groups-satisfy-boone-higman`.

Open: **D̃_n (`n >= 4`), Ẽ_6, Ẽ_7, Ẽ_8, F̃_4.**

## Three obstructions

1. **Combinatorial.** In the presentation-graph convention every Euclidean diagram is a complete graph (non-adjacent Coxeter nodes commute, label 2). So each open type is a complete atom: by `complete-artin-atoms-are-invisible-to-artin-combinatorics`, folding separations, hub cones, clone doubles, parabolic embeddings, LCM-homomorphisms and diagram folds with complete result cannot move it to a non-complete host. (A diagram fold such as Ẽ_6 → F̃_4 relates two open types; it would not remove the pair.)
2. **Toric.** By `euclidean-artin-toric-commensurability` each open type is in `B_A` iff its toric Weyl arrangement group is, and those arrangements (D_n, n >= 4; E_6, E_7, E_8; F_4) are not fiber-type (`weyl-toric-arrangements-b-d-e-f-are-not-fiber-type`). For comparison, the G_2 toric arrangement is not fiber-type either: in root coordinates `(u, v) = (t^a, t^b)` the hypertori are `u, v, uv, u^2 v, u^3 v, u^3 v^2 = 1`, and for each of the six choices of fibre direction some double point off the fibre torus exists (for example `(1, -1)` on `u = 1` and `u^3 v^2 = 1`, or `(-1, 1)` on `v = 1` and `u^2 v = 1`); G̃_2 is reached instead through BLIW.
3. **Garside and automatic structures.** McCammond--Sulway (arXiv:1312.7770, abstract read) embed every irreducible Euclidean Artin group in a group "with an infinite-type Garside structure". Infinitely many simple elements means the finite-type Garside biautomaticity theorem does not apply, and the normal-form boundary machinery of `rational-germ-singular-sets-are-finite-graph-path-spaces` and `thin-rational-actions-give-finite-germ-extensions`, which needs an automatic structure over a finite generating set, has no input from this embedding. Finite-type (or quasi-) Garside structures found in the literature cover Ã_n (Digne, arXiv:math/0402116, quasi-Garside) and C̃_n (Digne, arXiv:1002.4320), both already in `B_A`. No automatic structure for D̃_n (`n >= 4`), Ẽ_6--Ẽ_8 or F̃_4 was found (bounded arXiv search, author Digne, abstract level; MathSciNet not searched).

## What would unblock the route suggested for these types

- An automatic (ideally biautomatic) structure, over a finite generating set, for one of the open types, or for a finitely generated overgroup whose action on its normal-form boundary is rational. Then the decidable tests (E1′, E4′) of bh-free-51 can be run.
- Or a finite-type Garside structure on a finite-index subgroup or overgroup.
