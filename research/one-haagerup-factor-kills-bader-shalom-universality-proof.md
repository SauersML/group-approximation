---
rg: 2
id: one-haagerup-factor-kills-bader-shalom-universality-proof
kind: route
title: "Proof: a Kazhdan subgroup has relatively compact image in a Haagerup factor (Delorme-Guichardet), the Bader-Shalom projection is injective, and a finitely generated infinite simple group has no nontrivial map to a compact group"
target: one-haagerup-factor-kills-bader-shalom-universality
requires:
  - bader-shalom-normal-subgroup-theorem
  - delorme-guichardet-property-t-implies-fh
  - fg-infinite-simple-groups-are-minimally-almost-periodic
  - fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree
---

**Setting.** `Γ < G_1 × G_2` is as in `bader-shalom-normal-subgroup-theorem`
with `n = 2`. Each `G_i` is locally compact, hence Hausdorff. `Γ` carries the
discrete topology, so every homomorphism out of a subgroup of `Γ` is continuous.

**Item 1.** Let `Λ ≤ Γ` have property (T), and let `G_j` be Haagerup, with a
proper cocycle `b ∈ Z^1(G_j, π)`. The restriction `p_j|_Λ : Λ → G_j` is a
continuous homomorphism. By `delorme-guichardet-property-t-implies-fh`, item 3,
`p_j(Λ)` is relatively compact. So `K := cl p_j(Λ)` is compact. It is a
subgroup because the closure of a subgroup of a Hausdorff topological group is
a subgroup. By `bader-shalom-normal-subgroup-theorem`, item 2, `p_j` is
injective on `Γ`, hence on `Λ`.

**Item 2.** Suppose `Λ ≤ Γ` is infinite, finitely generated, simple and Kazhdan.
Item 1 gives an injective homomorphism `Λ → K` into a compact group. Since
`Λ ≠ 1`, this homomorphism is nontrivial. That contradicts
`fg-infinite-simple-groups-are-minimally-almost-periodic`, under which every
homomorphism from `Λ` to a compact group is trivial.

**Item 3.** Apply `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree` to
`Q = Z`, or to any finitely generated group with solvable word problem. It gives
an infinite, finitely generated, simple group `H` with property (T) and
`WP(H) ≤_T WP(Q)`, so `H` has solvable word problem. So `H` is an admissible
input `S` for P1. If P1 embeds `H` in some `Γ`, item 2 shows that neither `G_1`
nor `G_2` is Haagerup.

- *Non-compact:* put `L_i = cl p_i(H)`, a closed subgroup of `G_i`. If `L_i` were
  compact, then `p_i|_H : H → L_i` would be a nontrivial homomorphism to a
  compact group, since it is injective.
- *Not Haagerup:* if `L_i` were Haagerup, the argument of item 1 applied inside
  `L_i` would make `p_i(H)` relatively compact in `L_i`. Its closure `L_i` would
  then be compact, which the previous point excludes.

The same holds for every decidable simple input of the form `H_Q ⊇ Q`, by the
same host theorem.

**Where Attempt 1(b) of the target stopped short.** It bounded `ψ ∘ p_j` and
concluded `p_j(H) ⊆ K_j`, but used this only to intersect with the discrete
`Γ`. That needs both factors Haagerup. The one-factor case needs injectivity
(NST item 2) and minimal almost periodicity instead. ∎
