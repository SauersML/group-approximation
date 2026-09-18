---
rg: 2
id: one-stabilization-ac-trivial-from-primitive-relator
kind: claim
title: A two-generator balanced trivial presentation is AC-trivial after one stabilization once its relator pair reaches a primitive element of F_3 under relator-pair AC moves and automorphisms
distinct_from:
  z-presentations-with-a-trivializing-relator-are-ac-equivalent: that says the AC class of a deficiency-one Z-presentation plus a trivializing relator does not depend on the relator; this uses it to turn a primitive relator in the relator pair into a full AC-trivialization, with automorphisms of F_3 allowed along the way
  shehper-z-conjecture-iff-one-stabilization-ac: that is an equivalence between two universal statements; this is a sufficient criterion for one presentation, used as a search goal
  balanced-trivial-presentations-one-stabilization-ac-trivial: that is the open universal statement; this is a checkable certificate format for single instances
artifacts:
  - experiments/ak3-stable-primitive-search-2026-09-17/pzsearch.c
  - experiments/ak3-stable-primitive-search-2026-09-17/pzproj.c
---

**ESTABLISHED** through `one-stabilization-primitive-relator-criterion-proof`. Unreviewed.

Let S = ⟨a, b | s_1, s_2⟩ present the trivial group and let
S⁺ = ⟨a, b, c | s_1, s_2, c⟩ be its one-stabilization, in F = F(a, b, c).

Call (r_1, r_2) ∈ F² a **Z-pair** if ⟨F | r_1, r_2⟩ ≅ Z. The pair (s_1, s_2) is a
Z-pair. Allow two kinds of moves on Z-pairs:

- **(P1)** AC moves between r_1 and r_2 only: r_i ↦ r_i r_j^{±1} (i ≠ j), r_i ↦ r_i^{−1},
  and r_i ↦ g r_i g^{−1} for a letter g ∈ {a^{±1}, b^{±1}, c^{±1}};
- **(P2)** (r_1, r_2) ↦ (α(r_1), α(r_2)) for α ∈ Aut(F).

**Criterion.** If a finite sequence of moves (P1), (P2) carries (s_1, s_2) to a Z-pair
with a primitive element of F among its entries, then S⁺ is AC-trivial, i.e.
S is stably AC-trivial with a single stabilization.

The goal is weaker than reaching the trivial presentation. A primitive relator can
be tested in polynomial time with Whitehead's algorithm. Moves (P2) are not AC moves
but preserve AC-triviality.

**Projection form.** Let r be a Z-pair reached from (s_1, s_2) by moves (P1), (P2). Let g be
a generator whose 2 × 2 exponent-sum minor (the columns other than g) is ±1, and let P(r) be
the rank-2 presentation obtained by deleting g from both relators. Then S⁺ is AC-trivial
**iff** P(r)⁺ is AC-trivial (Step 5 of the route). The class of P(r)⁺ depends only on the
class of P(r) under rank-2 AC moves and automorphisms. Two consequences:
- By `short-balanced-trivial-presentations-are-trivial-or-ak3`, a projection P(r) of total
  length ≤ 12 certifies S⁺ AC-trivial.
- A projection in the rank-2 AC-plus-automorphism class of S itself certifies nothing.

**Use.** With S = AK(3), a certificate would establish `ak3-is-stably-ac-trivial`.
The search `pzsearch.c` explores this move graph with a total-length cap.
