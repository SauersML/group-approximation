---
rg: 2
id: one-stabilization-ac-trivial-from-thickenable-z-pair
kind: claim
title: A two-generator balanced trivial presentation is AC-trivial after one stabilization once its relator pair reaches an orientably thickenable Z-pair in F_3 under relator-pair AC moves and automorphisms
distinct_from:
  one-stabilization-ac-trivial-from-primitive-relator: that takes an algebraic endpoint (a primitive relator); this takes a topological endpoint (the 2-complex of the pair embeds in an orientable 3-manifold), which is not invariant under automorphisms and is reached where no primitive relator is
  thickenable-balanced-presentations-have-meridional-relators: that is about balanced presentations of the trivial group, where the thickening is a ball; this is about deficiency-one presentations of Z in rank 3, where the thickening is a solid torus, and gives a sufficient criterion rather than a necessary condition
  ak3-is-stably-ac-trivial: that is the open statement; this is a certificate format for it
artifacts:
  - experiments/ak3-thick-z-pair-search-2026-09-17/thzsearch.c
  - experiments/ak3-thick-z-pair-search-2026-09-17/thick2.c
  - experiments/ak3-thick-z-pair-search-2026-09-17/calibration.log
---

**Proposed ESTABLISHED** through `one-stabilization-thickenable-z-pair-criterion-proof`. Unreviewed.

Notation as in `one-stabilization-ac-trivial-from-primitive-relator`:
- S = ⟨a, b | s_1, s_2⟩ presents the trivial group, and S⁺ = ⟨a, b, c | s_1, s_2, c⟩ in
  F = F(a, b, c).
- A **Z-pair** is (r_1, r_2) ∈ F² with ⟨F | r_1, r_2⟩ ≅ Z.
- Moves: (P1) AC moves between r_1 and r_2 only, and (P2) automorphisms of F applied to
  both entries.

A Z-pair is **orientably thickenable** if its presentation 2-complex K (one vertex, three
edges, two 2-cells) embeds in some orientable 3-manifold. A generator that occurs in
neither relator contributes a wedge summand S¹. An orientable 1-handle keeps such a
complex thickenable, so absent generators can be ignored in the test.

## Criterion

If a finite sequence of moves (P1), (P2) carries (s_1, s_2) to an orientably thickenable
Z-pair, then S⁺ is AC-trivial.

**Projection form.** Let r be reached from (s_1, s_2) by moves (P1), (P2). Let g be a
generator whose exponent-sum minor m_g is ±1, as in Step 5 of
`one-stabilization-primitive-relator-criterion-proof`. If the rank-2 projection P(r) is
thickenable, then S⁺ is AC-trivial.

**Topological core (Theorem 1 of the route).** For an orientably thickenable Z-pair r:
- a regular neighbourhood N of K is a solid torus;
- a 2-handle along a longitude of N gives a 3-ball;
- that longitude reads a word w for which ⟨F | r_1, r_2, w⟩ is thickenable, so it is
  AC-trivial by Lackenby (arXiv:2606.06122, Thm 1.3).

## Why this is a different endpoint

- A primitive relator is an algebraic endpoint, invariant under Aut(F). Thickenability is
  not invariant under Aut(F). Every Z-pair with a primitive entry is AC/Aut-equivalent to a
  basis-like pair, which is thickenable. The converse fails.
  - Calibration on AK(2) at total-length cap 13 (`calibration.log`): the component holds
    9 thickenable pairs without a primitive entry.
  - With the primitive test switched off, `thzsearch.c` reaches a thickenable pair
    (xyx, x⁻²y⁻¹x⁻¹y⁻¹) from AK(2) after 70 states.
- The hypothesis ⟨F | r⟩ ≅ Z is essential. The pair (x², y³) is thickenable (a spine of a
  punctured lens-space connected sum), and it presents Z/2 ∗ Z/3 ∗ Z, not Z.
  `thzsearch.c` flags it at the start state.

## Necessary condition

`thickenable-z-pairs-split-quotient-meridian-obstruction` shows the following. In an
orientably thickenable Z-pair, if the one-relator quotient by r_i splits freely (for
instance when r_i is separable), then r_j is, modulo r_i, a meridian of a knot-group free
factor. Consequently, no route from the AK(n) pair that changes only one relator (up to
conjugation, inversion and Aut(F_3)) reaches this goal.

The hypothesis cannot be dropped. (x^{−1}y^{−1}, x^{−4}y^{−3}z^{−3}) is a thickenable Z-pair
whose second relator is not separable. So endpoints with no separable relator carry no
meridian condition, and they are not excluded by any Whitehead-graph filter.

**Use.** With S = AK(3), a certificate establishes `ak3-is-stably-ac-trivial`. `thzsearch.c` searches the AK(3) component for this goal,
the primitive goal and the projection goal together. The results are recorded in the
Attempts of `andrews-curtis-conjecture`.
