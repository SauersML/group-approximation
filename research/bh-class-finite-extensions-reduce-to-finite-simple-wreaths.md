---
rg: 2
id: bh-class-finite-extensions-reduce-to-finite-simple-wreaths
kind: claim
title: The Boone--Higman class is closed under finite extensions iff finite-simple wreaths of finitely presented simple groups embed, given squares
distinct_from:
  boone-higman-type-a-class-closed-under-finite-extensions: that proves closure under finite extensions for the permutational class B_A, where it is known; this is about the full Boone--Higman class, where closure is open, and reduces it to one statement about finitely presented simple groups.
  boone-higman-closed-under-finite-direct-products: that is closure under direct products, reduced there (Attempt 10) to joint embedding (JE) plus squares (SQ); this is closure under finite extensions, and combines with it.
artifacts:
  - research/artifacts/gq-bh-bh-permanence-closure-reductions.md
---

**ESTABLISHED** by `bh-class-finite-extensions-wreath-proof`
(lane proof, elementary, not independently reviewed; no priority claimed).

Let `𝓑` be the class of groups that embed in some finitely presented simple group.
It is closed under subgroups, contains every finite group, and its finitely
generated members have solvable word problem.

Consider three statements.
- **(FE)** `𝓑` is closed under finite extensions: if `H <= G`, `[G:H] < ∞` and
  `H ∈ 𝓑`, then `G ∈ 𝓑`.
- **(SQ)** `U x U ∈ 𝓑` for every finitely presented simple `U` (as in Attempt 10 of
  `boone-higman-closed-under-finite-direct-products`).
- **(FW)** For every finitely presented simple `S` and every finite simple group `Q`,
  the regular wreath product `S ≀ Q = S^Q ⋊ Q` lies in `𝓑`.

Then:
1. (FW) implies (FE).
2. (FW) implies (SQ), since `S x S <= S ≀ Z/2`.
3. (FE) and (SQ) together imply (FW).

So (FW) is equivalent to (FE) ∧ (SQ). With Attempt 10 of
`boone-higman-closed-under-finite-direct-products` (closure under finite direct
products ⟺ (JE) ∧ (SQ)), it follows that `𝓑` is closed under finite direct
products **and** finite extensions if and only if (JE) ∧ (FW) holds.

**What this changes.** Both closure questions become statements about finitely
presented simple groups alone: (JE), any two embed in a common one, and (FW),
their wreaths by finite simple groups embed. Only prime-order cyclic and
nonabelian finite simple tops `Q` are needed, with regular action.

**Calibration.** Every finitely presented simple `S` with the permutational
property (`S ∈ B_A`) satisfies the conclusion of (FW): `B_A` is closed under
finite direct products and finite extensions
(`boone-higman-type-a-class-closed-under-finite-extensions`), so `S^Q ∈ B_A`,
hence `S ≀ Q ∈ B_A ⊆ 𝓑`. So a failure of (FE) needs a finitely presented simple
group outside `B_A`, consistent with `bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`.

**Not claimed.** Any of (FE), (SQ), (FW), (JE) themselves; all four follow from
`boone-higman-conjecture` and are open.
