---
rg: 2
id: mapping-torus-targets-fail-rank-2-window-one-relators
kind: claim
title: For the 128 length-15 one-relators whose Magnus middle letter occurs once, every map to a residually torsion-free nilpotent group kills a, and a map to an ascending mapping torus of a finitely generated residually torsion-free nilpotent group needs a root of e2 x^2 + e1 x + e0 to be an eigenvalue of an integer matrix; so 32 words have no such target at all, 64 have none with an automorphic monodromy, and only 32 are left open
distinct_from:
  malcev-root-steps-put-commutator-root-one-relators-in-h: its item 3 kills residually-𝒮 targets for the e = (0, ±2, 0) and e = (0, -3, 0) frontier through the propagation of dead interior letters in segments; here e_0 + e_1 + e_2 is odd, a is torsion in H_1(G), and the obstruction is an eigenvalue condition on the monodromy of a target that contains F_2, for the other 128 open words of its item 2.
  edge-injective-quotients-give-hughes-free-division-rings: item 1 there is the lemma whose targets are excluded here; nothing about the lemma itself changes.
  kaplansky-zero-divisor-conjecture: no case of the conjecture changes; torsion-free one-relator groups already satisfy it (Higman; Brodskii, Howie).
artifacts:
  - experiments/non-residually-solvable-targets-2026-09-18/eigen_obstruction.py
  - experiments/non-residually-solvable-targets-2026-09-18/classify.py
  - experiments/non-residually-solvable-targets-2026-09-18/eigen-L15.txt
  - experiments/non-residually-solvable-targets-2026-09-18/w313-L15.txt
  - experiments/non-residually-solvable-targets-2026-09-18/fbc_batch.py
  - experiments/non-residually-solvable-targets-2026-09-18/fbc-L15.txt
  - experiments/non-residually-solvable-targets-2026-09-18/groups.py
  - experiments/non-residually-solvable-targets-2026-09-18/target_search.py
---

**ESTABLISHED** (written proof, unreviewed) by
[[mapping-torus-targets-fail-rank-2-window-one-relators-proof]]. Items 1 to 3 are obstructions, item 4 is
their count, and item 5 records searches that found nothing. Nothing is new for the zero-divisor conjecture.

**Setting.** This is the second length-15 shape of item 2 of
[[malcev-root-steps-put-commutator-root-one-relators-in-h]]: 128 relators `G = <a, t | r>` whose span-2
Magnus rewrite `r' ∈ F(a_0, a_1, a_2)` has occurrences `(3, 1, 3)`.
- The list is `w313-L15.txt`.
- `a_1` occurs once, so `r' = 1` reads `a_1 = V(a_0, a_2)`, and `G` is the HNN extension of `F(a_0, a_2)` along
  the rank-2 window `A = <a_0, a_1>`.
- A target for item 1 of [[edge-injective-quotients-give-hughes-free-division-rings]] is a map `φ: G -> Q`,
  with `Q ∈ 𝓗`, that is injective on `A ≅ F_2`, so in particular `φ(a) ≠ 1`.
- The exponent vector is `e = (e_0, e_1, e_2)` with `e_1 = ±1` and `e_0, e_2 ∈ {±1, ±3}`. Put
  `f(x) = e_2 x^2 + e_1 x + e_0`.
- `f` is primitive and irreducible, since its discriminant `1 - 4 e_0 e_2` is never a square, and
  `f(1) = e_0 + e_1 + e_2` is odd.

## Theorem

1. **No residually torsion-free nilpotent target.**
   - Every homomorphism from `G` to a residually torsion-free nilpotent group kills `a`. In particular it kills
     free groups, RAAGs, surface groups, and torsion-free nilpotent groups of any class.
   - Every map `G -> Z` kills `a` too, because `a` has order `|f(1)|` in `H_1(G) = Z ⊕ Z/f(1)`.
   - So neither a Mal'cev target (rule N) nor a map to `Z` (rules 1, R) can see the window.
2. **The eigenvalue condition.** Let `B` be finitely generated and residually torsion-free nilpotent, `ψ` an
   injective endomorphism of `B`, and `Q = B *_ψ = <B, s | s^{-1} w s = ψ(w)>`. Let `φ: G -> Q` have
   `φ(a) ≠ 1`, and let `m` be the `s`-exponent of `φ(t)`. Then:
   - `m ≠ 0`;
   - if `m > 0`, the roots of `f` are eigenvalues of an integer matrix: the action of `ψ^m` on a rational lower
     central quotient of `B`. Hence **`|e_2| = 1`**;
   - if `m < 0`, the same holds for the mirror polynomial `e_0 x^2 + e_1 x + e_2`. Hence **`|e_0| = 1`**.
3. **Mapping tori.** If `ψ` is an automorphism, so that `Q = B ⋊_ψ Z` (e.g. every free-by-cyclic group with
   finitely generated fibre), then both `|e_0| = |e_2| = 1`. The roots of `f` are then units, namely primitive
   3rd or 6th roots of unity (`x^2 ± x + 1`) or `±` the golden ratio and its conjugate (`x^2 ± x - 1`).
4. **Count** (`eigen_obstruction.py w313-L15.txt`, output `eigen-L15.txt`). The 128 words split as follows.
   - **32 with `|e_0| = |e_2| = 3`.** They have no homomorphism with `φ(a) ≠ 1` to any group of item 2,
     free-by-cyclic or ascending.
   - **64 with exactly one of `|e_0|, |e_2|` equal to `1`.** They have none to any `B ⋊ Z`. An ascending target
     needs a non-surjective `ψ` and the sign of `m` fixed by item 2.
   - **32 with `|e_0| = |e_2| = 1`,** 8 for each of `x^2 ± x ± 1`. Only these admit a free-by-cyclic target in
     principle. Its monodromy has, on some lower central quotient, finite order 3 or 6, or a golden-ratio
     eigenvalue.
5. **Searches (nothing found).**
   - **Free-by-cyclic and ascending targets** (`fbc_batch.py`, output `fbc-L15.txt`). The search runs over
     endomorphisms `ψ` of `F(x, y)` with non-commuting images and elements `g`, in both orientations and for
     all 128 words at once, using the abelian filter of item 2. It finds no `(ψ, g)` with
     `ψ g = V(g, ψ^2 g)` and `[g, ψ g] ≠ 1`. Three runs completed:
     - images of length at most 2 with `g` of length at most 6;
     - images of length at most 3 with `g` of length at most 4;
     - images of length at most 3 with `g` of length at most 5.
     A run with images of length at most 3 and `g` of length at most 6 did not finish within 1200 s, and
     nothing is claimed for it.
   - **Family C targets of Baumslag–Gersten type** (`target_search.py`, `groups.py`, Britton reduction). For the
     L14 family C (`e = (0, ε, 0)`), a single map `G -> Q` that is nontrivial on the top and bottom edge
     elements climbs every segment step. This is because the shifted edge elements are `φ(t)`-conjugates of
     those two. Item 3 of the Mal'cev node forces `Q` to be not residually solvable.
     - The search tried the Baumslag–Gersten group `<a, b | (a^b)^{-1} a (a^b) = a^2>`, and its analogues with
       `a^k`, as `Q`. For `AABaabAAbaBBaB` it found no `(φ(a), φ(t))` with `φ(a)` of length at most 6 and
       `φ(t)` of length at most 4.
     - The same search with `BS(2, 3)` found nothing either. That is expected, since `BS(2, 3)` is residually
       solvable.

## What is new, and what is not

- **Nothing for the zero-divisor conjecture.**
- Item 1 is the standard graded argument, recorded because it rules out the whole Mal'cev mechanism of rule N
  for this shape.
- Items 2 and 3 are new as a statement about this frontier. They cut the open part of the `(3, 1, 3)` shape from
  128 words to 32 for free-by-cyclic targets, and to 96 for ascending ones.

## Where it stops

- **The fibre must be big.** A target `Q ∈ 𝓗` for a KILL word, if one exists, is not residually torsion-free
  nilpotent. Every map `Q -> Z` either kills `φ(a)` or has a fibre that is not a finitely generated residually
  torsion-free nilpotent group, even up to ascending unions.
  - `G` itself is such a group: its fibre `N_G` is infinitely generated, an infinite amalgam of `F_2`'s along
    rank-2 windows. So nothing here decides whether `G ∈ 𝓗`.
- **The UNIT words** are the next test. A free-by-cyclic target needs monodromy whose action on the lower
  central quotient containing the leading term of `φ(a)` has an eigenvalue that is a primitive 3rd or 6th root
  of unity (for `x^2 ± x + 1`) or a golden-ratio unit (for `x^2 ± x - 1`).
  - Examples are the order-3 automorphism `x ↦ y ↦ (xy)^{-1}` and the Fibonacci automorphism `x ↦ xy, y ↦ x`
    of `F_2`. Both lie inside the item-5 search range (images of length at most 2), which found nothing.
- **Segment-level targets are not excluded.** Items 1 to 3 use the shift `t`: `a` is torsion in `H_1(G)`, and
  `φ(t)` acts on the fibre. They say nothing about maps `S_[0,n] -> Q` that are injective on the window of one
  step.
  - For example, `H_1(S_[0,1]) = Z^2` is free, because the `2 × 2` minors of its relation matrix have gcd `1`.
  - Such a `Q` still has to contain `F_2`, so it cannot be nilpotent.
  - `A ⊂ F(a_0, a_2)` is not a retract, because a rank-2 retract of `F_2` is all of `F_2`.
