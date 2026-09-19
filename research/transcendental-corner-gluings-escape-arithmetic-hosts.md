---
rg: 2
id: transcendental-corner-gluings-escape-arithmetic-hosts
kind: claim
title: For a transcendental p-adic unit u, the soluble minimax group G_u that glues the corners of two Hall–Heisenberg groups by multiplication by u admits no homomorphism, injective on its Prüfer radical, into any S-arithmetic corner host over a number field; so CGP Question 4 for computable transcendental u needs non-arithmetic isolated hosts
distinct_from:
  divisible-radicals-lie-in-the-fitting-commutator: that proves every Prüfer radical sits in a commutator corner; this shows that the gluing between two corners can be transcendental, which algebraic hosts cannot realize.
  s-unit-twisted-prufer-radicals-have-isolated-hosts: that realizes every algebraic (S-unit) twist; this names the first input whose corner data is not algebraic.
  every-decidable-group-embeds-in-an-isolated-group: that is CGP Question 4; this is a test case for it inside soluble minimax groups, where arithmetic hosts fail.
---

**OPEN** (stated by bh-free-60, 2026-09-19). The group `G_u` and its word-problem dichotomy are
due to lane bh-solvable (`fg-soluble-minimax-groups-can-have-unsolvable-word-problem`, 633eb2de3),
credited here.

## The group

Let `H = H(Z[1/p])` be the Heisenberg group with centre `Z(H) = Z[1/p]`, and let `t` act on
each of two copies by `(x, y, z) ↦ (px, p^(-1)y, z)`. Let `u ∈ Z_p^×`. Put

    G_u = (H × H) ⋊ ⟨t⟩ / C_u,     C_u = {(z_1, z_2) ∈ Z(H)^2 : z_1 − u z_2 ∈ Z_p}.

- **Radical.** `(z_1, z_2) ↦ z_1 − u z_2 mod Z_p` identifies `Z(H)^2/C_u` with `D ≅ Q_p/Z_p`,
  central and untwisted.
- **Word problem (bh-solvable).** `G_u` is finitely generated soluble minimax, and it has solvable
  word problem iff `u` is computable.
- **Two Hall subgroups.** Each copy `H_i` maps onto a Hall group `H/Z` whose corner is all of
  `D`. The two corners are identified by `D → D`, `d ↦ −u^(±1) d`. So `G_u` contains two copies of
  Hall's group glued along their Prüfer corners by the p-adic automorphism `u`.

## Claim

If `u` is transcendental over `Q`, then there is no homomorphism, injective on `D[p]`, from
`G_u` to a group `Γ` of `s-unit-twisted-prufer-radicals-have-isolated-hosts`, nor to any finite
product of them.

## Why it should hold (sketch, not a proof)

- **Injective on `D`.** A homomorphism injective on `D[p]` is injective on `D`, since every
  nonzero subgroup of `Q_p/Z_p` contains `D[p]`. So both Hall subgroups map with injective
  corners, and the gluing `u` is realized inside `Γ`.
- **Rigidity.** A homomorphism from `H(Z[1/p])` into the S-arithmetic unipotent-by-diagonal
  group `P` extends on the unipotent part to a morphism of rational Mal'cev completions. So on
  corners it is `Q`-linear. The map into `P/L`, rather than `P`, needs a lifting argument through
  the central extension `L → P → P/L`, which is not done here.
- **Conclusion of the sketch.** The corner of `Γ` is a sum of `K_𝔭/O_𝔭` with number-field
  structure. Both corner maps are then multiplication by algebraic `𝔭`-adic numbers `α_1, α_2`,
  and the gluing forces `u = −α_2/α_1` on a coordinate where `α_1 ≠ 0`. That is algebraic,
  contradicting the choice of `u`.

## Why it matters

- **A genuinely new host is needed.** For computable transcendental `u`, `G_u` is a finitely
  generated soluble minimax group with solvable word problem. Question 4 (and Boone–Higman)
  predicts an isolated overgroup. If the claim holds, no S-arithmetic corner host provides one:
  the corner gluing must be computable but not algebraic.
- **This is where decidability enters.** Soluble minimax inputs split in two:
  - algebraic corner data, handled by Kneser–Abels hosts, with no use of decidability;
  - transcendental computable gluings, where an isolated host must consume the computation of
    `u`, as the Boone–Higman route must (compare
    `free-product-emitter-full-groups-need-isolated-vertex-groups`).

## Lesson for general BH

**Arithmetic hosts see only algebraic gluing.**
- Every Prüfer radical of a soluble minimax group is a corner. Kneser–Abels hosts realize every
  algebraic twist and gluing of corners.
- But two corners can be glued by a transcendental p-adic unit `u`. Then the group is decidable
  exactly when `u` is computable, and (by the sketch) no arithmetic host carries it.
- So even inside soluble minimax groups, Question 4 and Boone–Higman must consume decidability.
  The smallest test is `G_u` with `u` computable and transcendental.
