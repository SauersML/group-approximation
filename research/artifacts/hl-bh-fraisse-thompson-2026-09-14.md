# hl-bh-fraisse-thompson (2026-09-14): Fraïssé Thompson groups for the Rado graph

Lane executing survivor 3 (idea 4) of `research/artifacts/ideas-bh-round2-2026-09-14.md`.

**Target.** A finitely presented oligomorphic actor on the Rado graph with finitely generated
stabilizers. That is a type (A) host not built on Cantor charts, and a candidate source of new
Boone–Higman inputs.

**Verdict.** Not decided. One barrier theorem is landed, computer-checked by two independent
implementations and not independently reviewed. The existence question and a finite-search
special case are landed as OPEN nodes. No piecewise-automorphism group was constructed, and no
finite presentation or simplicity was proved.

## 1. Source pins

**Type (A) and its payoff.** Zaremsky, arXiv:2405.18354: the four conditions, Theorem A and
Corollary B. These are already quoted verbatim in `type-a-action-gives-boone-higman-for-subgroups`
and were not re-read here.

**P. J. Cameron, "The Random Graph", arXiv:1301.7544v1.** PDF read locally, text extracted.
- p.1, verbatim:
  > "(∗) Given finitely many distinct vertices u1 , . . . , um , v1 , . . . , vn , there exists a
  > vertex z which is adjacent to u1 , . . . , um and nonadjacent to v1 , . . . , vn ."

  and
  > "Fact 2. Any two countable graphs satisfying (∗) are isomorphic."
- §1.8.3, verbatim:
  > "It is not true that, for every countable group G, a random Cayley graph for G is almost
  > surely isomorphic to R. Necessary and sufficient conditions can be given; they are somewhat
  > untidy."

  and
  > "Proposition 17. Suppose that the countable group G cannot be expressed as the union of
  > finitely many translates of non-principal square-root sets and a finite set. Then almost
  > all Cayley graphs for G are isomorphic to R."
- §1.8.4, verbatim:
  > "Theorem 11. There are exactly five reducts of R, viz.: A = Aut(R); the group D of
  > automorphisms and anti-automorphisms of R; the group S of switching automorphisms of R; the
  > group B of switching automorphisms and anti-automorphisms of R; and the symmetric group."

**Duchesne–Monod–Wesolek, arXiv:1801.09787, abstract, verbatim:**
> "Given a transitive permutation group, a fundamental object for studying its higher
> transitivity properties is the permutation action of its isotropy subgroup. We reverse this
> relationship and introduce a universal construction of infinite permutation groups that takes
> as input a given system of imprimitivity for its isotropy subgroup. This produces vast families
> kaleidoscopic groups. We investigate their algebraic properties, such as simplicity and
> oligomorphy; their homological properties, such as acyclicity or contrariwise large Schur
> multipliers; their topological properties, such as unique polishability. Our construction is
> carried out within the framework of homeomorphism groups of topological dendrites."

The abstract says nothing about finite generation or finite presentation. The body was not read.

**Pinsker–Rydval–Schöbi–Spiess, arXiv:2507.12078, abstract, verbatim:**
> "We prove that the random ordered graph is a semi-retract of the canonically ordered atomless
> Boolean algebra, hereby answering an open question of Bartošová and Scow."

"Semi-retract" was not read at source, so no relation to the theorem below is claimed.

**Correction to the ideas artifact.** Its parenthetical "Every countable group embeds in
Aut(Rado) (*unpinned*)" stays unpinned. The only statement read here is Proposition 17, a
sufficient condition for regular Cayley realizations, and Cameron says it does not hold for every
countable group. The embedding claim itself is neither pinned nor refuted.

## 2. Theorem landed

`v-invariant-clopen-graphs-are-never-the-rado-graph`, with route
`v-invariant-clopen-graph-rado-census-proof`.

**Statement.** For every group `D` with `V <= D <= Homeo(C)`, no `D`-invariant graph on the
nonempty proper clopen subsets of the Cantor set satisfies (∗) for three vertices. So none is the
Rado graph.

**Invariant graphs.** They are the 32 unions of five pair classes:

| bit | class | pattern `(U∩z, U\z, z\U, C\(U∪z))` |
|---|---|---|
| 0 | complementary | (0,1,1,0) |
| 1 | disjoint | (0,1,1,1) |
| 2 | nested | (1,0,1,1), (1,1,0,1) |
| 3 | covering overlap | (1,1,1,0) |
| 4 | generic overlap | (1,1,1,1) |

**Census.**
- MSI job 793013, `fraisse-rado-search.py`:
  - `K = 2`: 6 configurations, 8 surviving masks (6, 7, 12, 13, 18, 19, 24, 25).
  - `K = 3`: 174 configurations, 0 surviving.
  - `K = 4` with at most 8 atoms: 36,355 configurations, 0 surviving.
- MSI job 795198:
  - `fraisse-rado-certs.py` emitted one certificate per mask.
  - `fraisse-rado-verify.py` (explicit depth-3 families, all 65,534 depth-4 clopens, separate pair
    classifier) verified 30 of 30.
  - Positive control PASS: the 8 survivors pass (∗) at two points on all pairs of depth-2
    clopens.
  - Negative control PASS: a corrupted certificate is rejected.

**Certificate families** (cones `a, b` of depth 3):
- the 22 masks dying at two points use `{U, U^c}`;
- masks 6, 7, 24, 25 use `{(a∪b)^c, a, a^c}`;
- masks 12, 13, 18, 19 use `{(a∪b)^c, a, b^c}`.

**Human-readable core.** The class of `(U^c, z)` is a function of the class of `(U, z)`:
- disjoint ↔ nested;
- `U ⊂ z` ↦ covering overlap;
- covering overlap ↦ nested;
- generic ↦ generic.

So adjacency to a set and to its complement is tied in every invariant graph. Complementation
commutes with `D` and swaps disjoint with covering overlap; the survivor list is closed under that
swap.

**md5 of outputs (MSI = local copies):**
- `certs.jsonl` 75c10078812acf88a4c01f72595af3d4
- `verify.txt` 00bde7d92991ac1338d5fb8d4891315b
- `k2.txt` 000b71c1c9ae42c5ef26b9f5f93b491e
- `k3.txt` 675c3a7770d240e00c5dc48a8c15c3e3
- `k4a8.txt` 48f78e6405b4b26ea1dc3f1cf0bb8cf2

## 3. What this means for idea 4

- **Barrier.** The natural type (A) action of V, and of every finitely presented full Cantor group
  containing V (`fp-full-binary-cantor-groups-have-type-a-actions`), is not an action on the Rado
  graph.
- **Why prefix replacement does not transfer (informal, not landed).** V's charts glue maps along
  finite clopen partitions, and clopen sets have no relations between different parts. The Rado
  analogue, gluing isomorphisms along partitions into induced copies of R, need not preserve edges
  between parts. So those permutations are not automorphisms of R. Theorem 11 lists the closed
  overgroups of Aut(R).
- **Payoff caveat.** A type (A) actor on R gives Boone–Higman only for its own subgroups. If the
  actor is V itself (route `rado-type-a-action-from-v-tuple-sort`), it adds no new inputs. New
  inputs need an actor containing groups outside known type (A) actors, and nothing here constructs
  one.

## 4. Nodes landed

- `v-invariant-clopen-graphs-are-never-the-rado-graph` (claim, ESTABLISHED) and
  `v-invariant-clopen-graph-rado-census-proof` (route, `requires: []`).
- `some-fp-group-acts-on-the-rado-graph-with-type-a` (claim, OPEN).
- `some-v-invariant-graph-on-clopen-tuples-is-rado` (claim, OPEN).
- `rado-type-a-action-from-v-tuple-sort` (route): the tuple-sort claim plus
  `fp-full-binary-cantor-groups-have-type-a-actions` give the existence claim.

Scripts and outputs are under `experiments/bh-fraisse-rado/`.

## 5. Exact gap

1. **Tuple sorts (finite refutation searches).** For k = 2 atom patterns, a SAT encoding of (∗) at
   K = 3 and 4 over the orbits of unordered pairs of tuples. A positive answer needs a structural
   proof for all K.
2. **Host existence.** `some-fp-group-acts-on-the-rado-graph-with-type-a` for any finitely presented
   group. Candidates must not be Cantor-chart groups acting on clopen sorts that the search refutes.
3. **Not attempted:**
   - piecewise-automorphism groups of free-amalgamation Fraïssé limits (random tournament, random
     poset, Henson graphs);
   - their finiteness properties via a Stein–Farley complex;
   - simplicity via Epstein–Higman;
   - which groups embed in them.
4. **Unpinned:** that every countable group embeds in Aut(R); the kaleidoscopic groups' finiteness
   properties (body of arXiv:1801.09787).
