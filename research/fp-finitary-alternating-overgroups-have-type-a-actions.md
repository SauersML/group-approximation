---
rg: 2
id: fp-finitary-alternating-overgroups-have-type-a-actions
kind: claim
title: A finitely presented permutation group containing the finitary alternating group of its set acts with type (A)
distinct_from:
  fp-groups-with-a-locally-moving-simple-subgroup-are-isolated: that shows such a group is isolated (normal structure); this shows its action is of type (A) (finiteness of stabilizers), so the same host already satisfies the permutational Boone--Higman conclusion for every subgroup.
  fp-full-binary-cantor-groups-have-type-a-actions: that builds a type (A) action on clopen sets for full Cantor groups containing V; this is the finitary case, where the given action itself is of type (A), with no topology.
  lampshuffler-groups-are-not-fp2-over-q: that says a family of candidate finitary hosts is never finitely presented; this says that any finitary host which is finitely presented is automatically a type (A) actor.
---

**ESTABLISHED** by `finitary-alternating-overgroup-type-a-proof` (elementary hand proof,
not independently reviewed; no novelty claimed for the method).

## Statement

Let `X` be an infinite set, `Γ ≤ Sym(X)` a group with `Alt_fin(X) ≤ Γ`.
1. If `Γ` is finitely generated, every point stabilizer `Γ_x` is finitely generated.
2. There is exactly one `Γ`-orbit of two-element subsets of `X`.
3. Hence if `Γ` is finitely presented, the action of `Γ` on `X` is of type (A) in the
   sense of `type-a-action-gives-boone-higman-for-subgroups`.
4. So (Zaremsky, arXiv:2405.18354, Corollary B) every subgroup of such a `Γ` has
   solvable word problem and embeds in a finitely presented simple group.

## Examples

Houghton's groups `H_n`, `n ≥ 3`, on `Ω_n` (finitely presented by Brown, JPAA 44
(1987)); and `FSym(Ω) ⋊ SV_G` of
`finitary-symmetric-extensions-of-oligomorphic-actions-are-fp`.

## Consequence

Branch (fin) of `fp-groups-with-a-locally-moving-simple-subgroup-are-isolated` never
yields an isolated host outside the permutational Boone--Higman class; see
`permutational-boone-higman-iff-finitary-alternating-hosts` for the converse.

DERIVATION
finitary-alternating-overgroup-type-a-proof
