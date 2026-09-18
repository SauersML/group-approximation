---
rg: 2
id: edge-injective-quotients-give-hughes-free-division-rings
kind: claim
title: A graph of groups with vertex groups in H lies in H as soon as it maps to H injectively on edge groups, which puts cyclic-edge HNNs, root adjunctions and Magnus root towers of one-relator groups in H, while Higman's group shows the edge condition cannot be dropped
distinct_from:
  vertex-injective-quotients-give-hughes-free-division-rings: that needs a map to H injective on every vertex group and handles Magnus HNNs only when the base retracts onto an edge group; this needs injectivity only on edge groups (vertex groups assumed in H), and so certifies non-retractive Magnus HNNs such as <a,b | a^2 b a b a^2 b^-2>, whose edge groups are rank-two non-retracts.
  baumslag-gersten-group-is-hughes-free-embeddable: that treats one ascending HNN of BS(1,2) by a directed union of retract segments; this treats Magnus towers whose segments are root adjunctions, not retractions.
  higman-bs-amalgam-has-hughes-free-division-rings: that proves the four Baumslag-Solitar amalgams inside Higman's group are Hughes-free embeddable; this uses them, with Higman's perfectness, to show H is not closed under amalgamation along F_2.
  kaplansky-zero-divisor-conjecture: that is the conjecture; this enlarges, over every division ring and every crossed product, the class of groups known to have Hughes-free division rings, and so to satisfy the zero-divisor conjecture.
artifacts:
  - experiments/magnus-hnn-vertex-quotients-2026-09-17/hierarchy_certify.py
  - experiments/magnus-hnn-vertex-quotients-2026-09-17/census.py
  - experiments/magnus-hnn-vertex-quotients-2026-09-17/orbit_certify.py
  - experiments/magnus-hnn-vertex-quotients-2026-09-17/census-L11.txt
---

**ESTABLISHED** (new class, strict reduction, and one obstruction) by
[[edge-injective-quotients-give-hughes-free-division-rings-proof]].

**Setting.** `𝓗` is the class of hereditarily Hughes-free embeddable groups of
[[vertex-injective-quotients-give-hughes-free-division-rings]]: groups every subgroup of which is HFE, where HFE means
that every crossed product `E * Γ` over every division ring `E` has a Hughes-free division ring. `𝓗` is closed
under subgroups, extensions, directed unions and free products. It contains free groups and locally indicable
amenable groups such as `Z[1/n] ⋊ Z`.

**Theorem.**
1. **Edge-injective quotient lemma.** Let `G = π_1(G_v, G_e; Γ)` with every vertex group `G_v ∈ 𝓗`. If some
   `φ: G -> Q` with `Q ∈ 𝓗` is injective on every edge group, then `G ∈ 𝓗`. The kernel of `φ` is a free product
   of subgroups of conjugates of vertex groups and a free group. Conversely `G ∈ 𝓗` gives `φ = id`. Item 2 of
   [[vertex-injective-quotients-give-hughes-free-division-rings]] is the special case in which `φ` is injective
   on vertex groups.
2. **Cyclic edge groups.** Let `B ∈ 𝓗`, let `a, c ∈ B` have infinite order, and let `G = B *_{a ↦ c}` be the
   HNN extension. If some `f: B -> Z` has `f(a) f(c) ≠ 0`, then `G ∈ 𝓗`. The target is
   `Z[1/(f(a)f(c))] ⋊ Z`, with `t` acting as multiplication by `f(c)/f(a)`. Consequences:
   - `BS(p,q) ∈ 𝓗` for all `p, q ≠ 0`.
   - For every word `w(x,y)` involving both letters, `<a,t | w(a, t^{-1} a t)> ∈ 𝓗` if and only if
     `<x,y | w> ∈ 𝓗`. This is a strict reduction of every Magnus HNN of span one to its base.
3. **Root adjunction.** Let `P ∈ 𝓗`, `g ∈ P` and `k ≥ 1`. If some `f: P -> Z` has `f(g) ≠ 0`, then
   `P *_{g = s^k} <s> ∈ 𝓗`. For a one-relator group this is the root rule: if `w` lies in `<X, b^k>`, then
   `<X, b | w> = <X, s | w_k> *_{s = b^k} <b>`. So `<X, b | w> ∈ 𝓗` whenever `<X, s | w_k> ∈ 𝓗` and the exponent
   vector of `w_k` is not a nonzero multiple of the `s`-coordinate.
4. **Root-tower theorem.** Let `G = <a,t | r>`, with `t` of exponent sum zero in `r`. Let
   `r' ∈ F(a_0, …, a_m)`, `m ≥ 1`, be its Magnus rewrite with `a_i = t^{-i} a t^i`, and let `e_j` be the exponent
   sum of `a_j` in `r'`. Suppose `a_m` occurs in the cyclic word `r'` in a single syllable, and
   `(e_0, …, e_{m-1}) ≠ 0`. Then `G ∈ 𝓗`. The same holds with `a_0` in place of `a_m` and `(e_1, …, e_m) ≠ 0`.
   The base retracts onto no edge group in general, and the edge groups have rank `m`.
5. **The explicit non-retractive example.** `G1 = <a,b | a^2 b a b a^2 b^{-2}>` lies in `𝓗`. Its relator is not
   primitive and not a proper power, so it has primitivity rank 2. Its Magnus rewrite is `a_0^2 a_1 a_2^2`, so
   `B = F(x,z)` with `x = a_0` and `z = a_2`. The edge groups are `A = <x, z^2>` and `C = <x^2, z>`, both of
   rank 2. Neither is a retract of `B`, because `z^2` has no square root in `A`. So item 6 of
   [[vertex-injective-quotients-give-hughes-free-division-rings]] does not apply. Item 4 does.
6. **Obstruction: `𝓗` is not closed under amalgamation along `F_2`.** In Higman's group
   `Hig = G_1 *_{F_ac} G_2` ([[higman-group-splits-as-amalgams-over-free-subgroups]]), both `G_1` and `G_2` lie in
   `𝓗`, and `F_ac ≅ F_2`. But `Hig` is perfect and nontrivial, so it is not locally indicable, and it is not in
   `𝓗`. Every map from `Hig` to a group of `𝓗` is trivial, and so it is not injective on `F_ac`.
   - So the hypothesis of item 1 cannot be weakened to "vertex groups in `𝓗`".
   - The embedding problem of item 3 of [[vertex-injective-quotients-give-hughes-free-division-rings]] has
     negative instances with free, finitely generated edge group.
   - Any proof that torsion-free one-relator groups lie in `𝓗` must use more than "vertex groups in `𝓗`, edge
     groups free".
7. **Decisive computation.** `hierarchy_certify.py` certifies membership in `𝓗` using only the free, Nielsen
   and retraction steps of the repository and items 2–4 above.
   - Every torsion-free two-generator one-relator group whose cyclically reduced relator has length at most 10
     lies in `𝓗`.
   - At length 11, the census (up to rotation, inversion and relabelling) certifies all but the 8 relators listed
     in `census-L11.txt`. At length 12 it certifies all but 73.
   - Retractions alone (mode `old`) miss 4, 24, 63 and 198 relators at lengths 7, 9, 10 and 11.

**What is new.** The vertex-injective criterion asks the quotient to see whole vertex groups. Magnus bases of
one-relator groups are the obstacle there: they are free-by-something with edge groups that are not retracts.
Item 1 asks only for the edge groups to survive. The kernel then still acts on the Bass–Serre tree with trivial
edge stabilizers, so it is a free product of groups already in `𝓗`. For Magnus towers the segments are root
adjunctions. The quotient needed at each step is a single homomorphism to `Z`, and its existence is a
linear-recurrence statement about `H_1`.

**Where it stops.**
- The 8 open relators of length 11 all have zero-exponent rewrites with rank-2 edge groups, in which both extreme
  letters occur in at least two syllables. Their Nielsen orbits, searched up to length 14 by `orbit_certify.py`,
  contain no certified relator.
- For these relators, no edge-injective map from the Magnus HNN to a free group was found (images of length ≤ 4).
- I have not checked whether Jaikin-Zapirain and Linton's work on group algebras of one-relator groups already
  gives HFE, over arbitrary division rings and crossed products, for all torsion-free one-relator groups. If it
  does, items 2–5 and 7 are special cases of it, and items 1 and 6 still stand.
