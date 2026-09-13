# Novelty check: B_n is self-similar iff n ≤ 3 (Zaremsky Problem 3.9, first question), 2026-09-13

Requested by z-verify-groups after its review PASS (`research/artifacts/zp-review-groups-2026-09-13-part2.md` §10,
d228d90964) of `braid-group-self-similar-iff-at-most-three-strands` (lane z3-09-braid-self-similar, 822b3ac5f2).

## Verdict

- **n ≥ 4 (B_n is not self-similar): NEW within the sources checked (bounded).**
- **n ≤ 3 (B_3 is self-similar): PRIOR RESULT.** "B_3 is self-similar" is a special case of Kochloukova,
  arXiv:2603.14556, Theorem 1.1 (15 Mar 2026), which predates the list's July 2026 version. That paper does not name
  B_3. The lane's explicit action on T_12, transitive on the first level, may still be new as a construction.
  Credit Kochloukova in `braid-groups-on-at-most-three-strands-are-self-similar` and in the relay wording.

## The positive half is covered by Kochloukova

D. H. Kochloukova, "Self-similarity of the generalized Baumslag-Solitar groups", arXiv:2603.14556v1 (15 Mar 2026). The
quotes below come from a fetch of the arXiv HTML; the owner lane should re-read them before citing.

- **Definition:** a generalized Baumslag–Solitar group of rank n is given by "finite graphs of groups with vertex and
  edge groups isomorphic to ℤⁿ such that all edge groups have finite index in the corresponding vertex groups",
  over a connected graph.
- **Self-similar:** "a group G admitting a faithful, self-similar action on m-ary rooted tree", state-closed.
  Intransitive actions are allowed, through families of virtual endomorphisms.
- **Theorem 1.1:** "Let G be a generalized Baumslag-Solitar group of rank n. Then the following conditions are
  equivalent: i) G is self-similar; ii) G is residually finite; iii) G is linear over ℚ."

B_3 = ⟨a, b | a² = b³⟩ is the amalgam ℤ *_ℤ ℤ over one edge, with the edge group of index 2 and 3 in the two vertex
groups. So it is a GBS group of rank 1. B_3 is residually finite: it is linear, since the Burau representation is
faithful for n = 3; alternatively, it is virtually F_k × ℤ, being a central extension of PSL₂(ℤ). Theorem 1.1 then
gives a faithful state-closed action of B_3 on a regular rooted tree. Per the fetch, the paper never mentions B_3,
torus knot groups or groups ⟨a,b | a^m = b^n⟩. Whether her action for B_3 is transitive on the first level was not
checked.

## Evidence for the negative half

1. **Zaremsky's list, version of July 12, 2026, Problem 3.9** (added 5/18/24): "Are braid groups self-similar?" is
   still asked.
2. **Citations of Dantas–Santos–Sidki, "Intransitive self-similar groups", arXiv:2004.08941** (J. Algebra 2020),
   Semantic Scholar, 9 entries. None concerns braid groups by title:
   - arXiv:2609.01868, Almeida–Dantas–Oliveira-Tosti (1 Sep 2026): permutational wreath products,
     PSL₂(ℤ[1/p]), Boone–Higman embeddings. Its HTML does not mention braid groups.
   - arXiv:2603.14556, Kochloukova (above).
   - arXiv:2509.16947: torsion-free nilpotent groups.
   - arXiv:2509.05798: non self-similar metabelian groups.
   - arXiv:2405.16678 (J. Algebra 2025): wreath products inside automata groups.
   - arXiv:2110.02441: self-similar abelian groups.
   - "Virtual endomorphisms of the group pg".
   - "On a class of self-similar polycyclic groups" (J. Algebra 2026).
3. **Sidki's works on self-similar groups** (OpenAlex, author and title search, 7 works: FP_n, products, Lie algebras,
   abelian centralizers, intransitive, polycyclic): no braid, Artin or mapping class groups.
4. **Citations of Bell–Margalit**, "Braid groups and the co-Hopfian property" (J. Algebra 2006; OpenAlex, 41 works),
   **and of Behrstock–Margalit**, "Curve complexes and finite index subgroups of mapping class groups" (Geom. Dedicata
   2006, arXiv:math/0504328; OpenAlex, 41 works).
   - The titles concern co-Hopfian properties, injections of Artin and mapping class groups, rigidity of curve and pants
     complexes, commensurators, and endomorphisms of Artin groups.
   - None mentions self-similar actions, rooted trees, automata or virtual endomorphisms.
   - I found no one applying Bell–Margalit or Behrstock–Margalit rigidity to virtual endomorphisms of B_n.
5. **OpenAlex title-and-abstract searches:**
   - "self-similar" AND "braid group": 13 works;
   - "self-similar" AND "Artin": 18 works;
   - "automaton group" AND "braid": 2 proceedings volumes;
   - "virtual endomorphism" AND "braid": 1 unrelated work.
   The only group-theoretic hit is "Braiding groups of automorphisms and almost-automorphisms of trees"
   (arXiv:2109.13389; Canad. J. Math. 2023). It introduces braided versions of self-similar groups; it does not give
   self-similar actions of braid groups.

## Bounds

- The session's web-search budget was exhausted: only API citation lists, arXiv abstract/HTML pages and the fetch
  tool's quotes were used.
- Citing works were checked by title except those named.
- No MathSciNet, zbMATH or Google Scholar.

## Recommendations

- **Owner lane:**
  - add Kochloukova arXiv:2603.14556 Theorem 1.1 to `braid-groups-on-at-most-three-strands-are-self-similar`, citing
    B_3 as a rank-1 GBS group;
  - keep the explicit transitive T_12 construction, described as a construction, not a first proof of
    self-similarity.
- **Relay wording:** "B_n is self-similar iff n ≤ 3. That B_3 is self-similar follows from Kochloukova's
  classification of self-similar GBS groups (arXiv:2603.14556, Thm 1.1). The non-self-similarity of B_n for n ≥ 4 is
  new within the sources checked. Together they answer the first question of Zaremsky's Problem 3.9."
- **Credit:** Kochloukova; Behrstock–Margalit (Thm 3) and Bell–Margalit; Dantas–Santos–Sidki (the criterion for
  intransitive actions); Nekrashevych–Sidki (virtual endomorphisms).
