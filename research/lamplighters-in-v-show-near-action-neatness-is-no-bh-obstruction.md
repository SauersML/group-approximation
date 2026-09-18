---
rg: 2
id: lamplighters-in-v-show-near-action-neatness-is-no-bh-obstruction
kind: claim
title: Lamplighters F wr Z lie in Thompson's group V but admit non-neat near actions, so no near-action neatness or profinite finite presentability condition on the input is necessary for Boone--Higman
distinct_from:
  simple-envelope-forces-solvable-word-problem: that is the one known necessary condition for embedding into a finitely presented simple group; this shows a whole family of candidate further conditions (from Cornulier's theory of near actions) is not necessary.
  bh-type-a-class-closed-under-permutational-lamp-wreaths: that builds finitely presented simple hosts for lamp wreaths; this only uses the elementary embedding of F wr Z into V, as a calibration.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-cornulier-reading.md
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no novelty claimed. Cornulier,
arXiv:1901.05065, remarks after his Proposition `notfp` that neatness does not pass to
finitely generated subgroups; this node records the instance relevant to Boone--Higman.)

## Statement

Let `F` be a nontrivial finite group.

1. `F wr Z = (⊕_{n∈Z} F) ⋊ Z` embeds in Thompson's group `V`, which is finitely presented
   and simple.
2. `F wr Z` is not profinitely finitely presented (Cornulier, Example in §`dig_pfp`, the
   lamplighter example). Hence, by Cornulier's Proposition `notfp`, it admits a sparse near
   action that is not realizable, not completable and not neat.

Consequently none of the following is a necessary condition for a finitely generated group
with solvable word problem to embed in a finitely presented simple group:
- every near action of the input is neat (Cornulier's conclusion for finitely presented
  groups, his Theorem `nearactionfp`);
- every sparse near action of the input is completable, or realizable;
- the input is profinitely finitely presented.

So Cornulier's structure theorem for near actions of finitely presented groups gives no
necessary condition on Boone--Higman inputs. A near-action obstruction to Boone--Higman would
have to use near actions of the host that are not determined by the input, together with some
property of finitely presented simple groups beyond finite presentation (for instance: every
near action of an infinite simple group is balanced, since its index character is a
homomorphism to Z).

## Proof

1. `V` acts on the Cantor set `C = {0,1}^N` by prefix replacements. Pick `t ∈ V` and a
   nonempty clopen `U` with the translates `t^n U`, `n ∈ Z`, pairwise disjoint. For example,
   in the dyadic interval model take the standard generator `x_0 ∈ F ≤ V`, which fixes `0`
   and `1` and has no other fixed points, and a fundamental domain `U = [a, x_0(a))` with
   dyadic `a`. The subgroup `V_U` of elements supported in `U` is isomorphic to `V` and
   contains every finite group (permute finitely many disjoint cones inside `U`). Choose a
   faithful copy `F_0 ≤ V_U` of `F`. The conjugates `t^n F_0 t^{-n}` are supported in the
   pairwise disjoint sets `t^n U`, so they commute and generate `⊕_n F`, with `t` shifting the
   index. An element `f t^k` with `f ∈ ⊕_n F` and `k ≠ 0` moves `U` onto the disjoint set
   `t^k U`, so it is nontrivial. Hence `⟨F_0, t⟩ ≅ F wr Z`. Finite presentation and simplicity
   of `V` are classical (Higman; Cannon--Floyd--Parry).
2. Cornulier's lamplighter example: if `Γ` is finitely presented and maps onto `F wr Z^d`,
   then (by the result he cites as [CGD]) a finite-index subgroup of `Γ` maps onto
   `F * Z^d`, so the profinite completion of `Γ` satisfies no group identity, unlike that of
   `F wr Z^d`. So no finitely presented cover induces an isomorphism of profinite
   completions. His Proposition `notfp` then gives a sparse near action that is not neat.
   Both statements were read at source; see the artifact for the exact labels and lines.
