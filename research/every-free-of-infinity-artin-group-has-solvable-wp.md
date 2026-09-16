---
rg: 2
id: every-free-of-infinity-artin-group-has-solvable-wp
kind: claim
title: Every Artin group whose Coxeter graph has only finite labels has solvable word problem
distinct_from:
  every-artin-group-has-solvable-word-problem: that is the word problem for every Artin group; this is the case with all labels finite, to which that one reduces by artin-word-problem-reduces-to-free-of-infinity-graphs.
  every-free-of-infinity-artin-group-is-type-f-infinity: that is a finiteness property of classifying spaces for the same graphs; this is solvability of the word problem, and neither is known to imply the other.
  free-of-infinity-artin-groups-satisfy-k-pi-1: that is asphericity of the Salvetti complex for the same graphs; a type-F group can have unsolvable word problem, so it does not give this.
---

**Statement.** Let `Γ` be a Coxeter graph on a finite set `S` with `m_st < ∞` for all
`s, t ∈ S`. Then the Artin group `A_Γ` has solvable word problem.

**Relation to Charney's Problem 10.**
- The route `artin-solvable-word-problem-from-free-of-infinity-case` derives
  `every-artin-group-has-solvable-word-problem` from this claim, through
  `artin-word-problem-reduces-to-free-of-infinity-graphs`.
- The converse is a special case, so the two statements are equivalent.
- Through `self-twisted-bt-group-fp-embedding-iff-solvable-wp`, both are equivalent to
  the yes answer to Zaremsky Problem 3.8.

**Reduction to irreducible graphs.** The *Dynkin diagram* of `Γ` has vertex set `S` and
an edge for each pair with `m_st ≥ 3`. Let `S_1, …, S_k` be its components.
- By the lemma in `artin-wp-from-covered-maximal-free-of-infinity-subgraphs-proof`,
  `A_Γ ≅ A_{Γ_{S_1}} × ⋯ × A_{Γ_{S_k}}`.
- A word is trivial exactly when each of its projections is trivial.
- So this claim is equivalent to its case with a connected Dynkin diagram.

**Cases the graph does not yet cover.** Suppose `Γ` is free of infinity with a connected
Dynkin diagram. The graph records a solvable word problem for `A_Γ` in these cases:
- `|S| ≤ 3`;
- `W_Γ` finite;
- `Γ` affine;
- `Γ` of cyclic type;
- no three distinct `x, y, z` with `m_xy = 3`, `m_xz = 2` and `m_yz ∈ {2, 3, 4}`.

The sources are `known-artin-classes-have-solvable-word-problem` and
`no-a3-b3-and-cyclic-type-artin-groups-have-solvable-wp`.
- The last class contains the right-angled, large-type and 2-dimensional cases.
- For graphs with only finite labels, type FC is the same as spherical type.

A connected free-of-infinity graph is therefore not covered by the graph exactly when:
- `|S| ≥ 4`;
- `W_Γ` is infinite and not affine;
- `Γ` is not of cyclic type;
- some `x, y, z` satisfy `m_xy = 3`, `m_xz = 2` and `m_yz ∈ {2, 3, 4}`.

Examples come from the compact hyperbolic Coxeter simplex groups, all of whose proper
parabolic subgroups are finite:
- rank 4: `[4,3,5]`, `[5,3^{1,1}]` and `[3,5,3]`; the last is covered under the larger
  reading below;
- rank 5: `[5,3,3,3]`, `[5,3,3,4]`, `[5,3,3,5]` and `[5,3,3^{1,1}]`.

The script `experiments/zaremsky-3-08-artin-wp-gap-census-2026-09-16/census.py` counts the
rank-4 gap up to relabelling of the generators.
- With labels at most 5 there are 276 classes, of which 92 are uncovered.
- With labels at most 6 there are 900 classes, of which 209 are uncovered.
- Under the diagram reading of Blasco-García–Cumplido–Holt–Morris-Wright–Rees below, the
  counts are 79 and 172.

The census is a finite illustration, not a classification.

**Reading of the rewriting theorem.** Theorem 1.1 of arXiv:2412.12195 excludes "A_3 or
B_3" subdiagrams. The paper's own usage, "(2,3,3) triangle (A_3 subdiagram)" and
"(2,3,4)-triangles", supports the class with `m_yz ∈ {3, 4}`. The graph imports only the
smaller class with `m_yz ∈ {2, 3, 4}`, which satisfies the hypothesis under every reading.
If the larger class is accepted, 13 of the 92 rank-4 classes with labels at most 5 move out
of the gap, `[3,5,3]` among them.

## Attempts

- 2026-09-16, lane swarm-zaremsky-3-08-twisted-brin-tho.
  - **Class-by-class import.** Imported the rewriting theorem of Blasco-García, Cumplido,
    Holt, Morris-Wright and Rees and the cyclic-type Garside theorem of Haettel–Huang
    (`no-a3-b3-and-cyclic-type-artin-groups-have-solvable-wp`). Assembled them along
    infinite labels (`artin-wp-from-covered-maximal-free-of-infinity-subgraphs`). This
    stops at the gap above.
  - **The K(π,1) conjecture does not help directly.** A type-F group can have unsolvable
    word problem (`some-type-f-group-has-unsolvable-word-problem`). So the K(π,1) results
    for rank 4 and dimension 3 give no algorithm. Theorem 5.6 of Godelle–Paris,
    arXiv:1007.1365, assumes both the K(π,1) property and solvable word problems for all
    free-of-infinity parabolic subgroups. So it takes the missing cases as input and adds
    nothing here.
  - **Colimit over proper parabolic subgroups.** For `|S| ≥ 3`, `A_Γ` is the colimit of
    the `A_T` over proper subsets `T`, since every relation involves two generators. Dies
    at: no normal form theorem for such a colimit was found without curvature hypotheses
    on the Deligne complex. Such hypotheses are recorded in the graph only for types
    already covered. Work of R. Charney on locally reducible Artin groups was not
    fetched. The exact reference and any word-problem consequence are unverified.
  - **An explicit finitely presented host of `AV_A`** (artifact
    `research/artifacts/zp-z3-08-twisted-bt-artin-2026-09-13.md` §6). By
    `self-twisted-bt-group-fp-embedding-iff-solvable-wp` this is equivalent in strength,
    so it is a construction strategy, not a reduction.
  - **Extending the rewriting system.** Dies at `B_3`-type triples. Example
    "n_atleast5" of arXiv:2412.12195 "shows that the condition that excludes B_3
    subdiagrams […] is necessary for our algorithm". The paper also says the condition
    `m_bc ≥ 5` "is built into" its Definition P3G.
  - **Haettel–Huang gluing theorem** (arXiv:2305.11622, Theorem F, source label
    `thm:intro garside`). It
    requires each complete subgraph of the Coxeter presentation graph to be a join of a
    cyclic-type graph and a spherical-type graph. For a free-of-infinity graph, the
    presentation graph is complete, so it gives only products of one cyclic-type and one
    spherical-type group. Those are already covered.
  - **Embedding into a covered Artin group.** An injective homomorphism into a group with
    solvable word problem would be enough, and LCM-homomorphisms between Artin groups are
    a candidate. This is an idea only; no uncovered group was mapped.
