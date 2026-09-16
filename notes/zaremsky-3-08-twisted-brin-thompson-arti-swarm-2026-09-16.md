# Zaremsky Problem 3.8: swarm lane note, 2026-09-16

Lane `swarm-zaremsky-3-08-twisted-brin-tho`. Root
`zaremsky-3-08-twisted-brin-thompson-artin-in-fp-group`. Locked hole:
`every-artin-group-has-solvable-word-problem`.

## Setup

- By `self-twisted-bt-group-fp-embedding-iff-solvable-wp` (conditions (1)–(4)), `AV_A`
  embeds in a finitely presented group if and only if `A` has solvable word problem.
- So the yes answer to Problem 3.8 is equivalent to Charney's Problem 10,
  `every-artin-group-has-solvable-word-problem`. I worked on that hole.
- The no answer would need an Artin group with unsolvable word problem. I did not work on
  it.

## What was added to the graph

Five claims and five routes, all in `research/`.

1. `artin-word-problem-reduces-to-free-of-infinity-graphs` (claim) with direct route
   `artin-word-problem-free-of-infinity-citation`.
   - **Novelty.** For the "all graphs" form, this is Theorem C of Godelle–Paris,
     arXiv:1105.1048. It is not new. I first thought the reduction was my own and then
     found it in the survey. It is credited as such.
   - **What was checked.** I reran the survey's induction for one graph `P(n)`, with the
     hypothesis only on free-of-infinity subsets of that graph, and passed from all
     free-of-infinity subsets to the maximal ones through van der Lek injectivity (quoted
     from the survey).
   - **Unread ingredients:**
     - the proof of the normal form theorem for amalgams (Theorem 3.3, credited to Serre);
     - the proof of Theorem 3.5, the membership algorithm. It comes from Godelle–Paris,
       arXiv:1007.1365, Prop. 2.7. I read that proposition and its proof but not Lemma 2.6
       or the construction of the retraction `π_T` it uses.
2. `every-free-of-infinity-artin-group-has-solvable-wp` (new hole, with `## Attempts`),
   and route `artin-solvable-word-problem-from-free-of-infinity-case` into
   `every-artin-group-has-solvable-word-problem`.
   - This is an equivalence, but it narrows the hole to graphs with only finite labels.
   - By the product lemma it narrows further to connected Dynkin diagrams.
3. `no-a3-b3-and-cyclic-type-artin-groups-have-solvable-wp` (claim) with direct route
   `no-a3-b3-and-cyclic-type-artin-wp-citation`. It imports two classes that
   `known-artin-classes-have-solvable-word-problem` does not record.
   - **(1) No conservative triple** (no `x, y, z` with `m_xy = 3`, `m_xz = 2`,
     `m_yz ∈ {2,3,4}`). From Blasco-García–Cumplido–Holt–Morris-Wright–Rees,
     arXiv:2412.12195v2, Theorem 1.1 and the detailed theorem. The route contains a written
     check that the class satisfies the hypothesis under every reading, including a full
     proof that `st` has order `m_st` in `W`.
   - **(2) Cyclic type.** From Haettel–Huang, arXiv:2305.11622v2: Theorem E (`A_Γ × Z` is
     Garside) plus Theorem D, item "solvable word and conjugacy problems".
     - The letters D, E, F were worked out from the LaTeX counters (`mthm` with `\Alph`).
       A first draft said "Theorem 1.3" without checking; that was corrected.
4. `artin-wp-from-covered-maximal-free-of-infinity-subgraphs` (claim) with route
   `artin-wp-from-covered-maximal-free-of-infinity-subgraphs-proof`.
   - The route contains a full proof of the product lemma and applies the maximal-subset
     reduction.
   - It covers new graphs, for example two `(3,3,3,4)` 4-cycles glued at a vertex with `∞`
     on the other cross pairs. That graph has rank 7, is not FC and has dimension 3.
5. `covered-artin-twisted-bt-groups-embed-in-fp-groups` (claim) with route
   `covered-artin-twisted-bt-groups-embed-in-fp-groups-proof`.
   - This is the partial yes answer to Problem 3.8 extended to the graphs of item 4.

## The refined gap

A connected, free-of-infinity Coxeter graph is not covered by anything in the graph
exactly when all of the following hold:
- `|S| ≥ 4`;
- `W_Γ` is infinite and not affine;
- `Γ` is not of cyclic type;
- `Γ` contains a conservative triple.

The following facts support this:
- For graphs with only finite labels, FC is the same as spherical.
- Right-angled, large-type and 2-dimensional graphs contain no conservative triple, since
  `(3,2,m)` with `m ≤ 5` is spherical.
- Joins along label 2 reduce to the components.

**Examples** (compact hyperbolic simplex groups):
- rank 4: `[4,3,5]` and `[5,3^{1,1}]`, plus `[3,5,3]`, which is uncovered only under the
  conservative reading;
- rank 5: `[5,3,3,3]`, `[5,3,3,4]`, `[5,3,3,5]` and `[5,3,3^{1,1}]`;
- the five cyclic-diagram hyperbolic tetrahedra are covered: `(3,5,3,5)` by (1), the other
  four by (2).

**Census.** The script is
`experiments/zaremsky-3-08-artin-wp-gap-census-2026-09-16/census.py`. It is
single-threaded, runs in seconds, and its outputs sit next to it.
- It enumerates Coxeter matrices on 4 generators up to relabelling, with labels in
  `{2, …, MAXLAB}`.
- It tags each class in the order reducible → spherical → affine → no triple → cyclic
  type → UNCOVERED. A disconnected Dynkin diagram counts as reducible, and its
  components of rank at most 3 are covered.
- Finiteness and affineness are decided from the smallest eigenvalue of the cosine Gram
  matrix, with `TOL = 1e-9`. The smallest nonzero `|eigenvalue|` seen was about
  `5.5e-3`, well above the tolerance.
- Results:
  - labels `≤ 5`: 276 classes, 92 uncovered (conservative reading) or 79 (diagram
    reading);
  - labels `≤ 6`: 900 classes, 209 or 172 uncovered.
- The rank-5 examples above were checked to be Lannér (connected, indefinite Gram matrix,
  every 4-vertex subdiagram spherical) and UNCOVERED. The rank-5 cycle `[(3^4,4)]` is
  cyclic type.
- This is a finite illustration, not a classification.

## Reading of the rewriting theorem (arXiv:2412.12195)

- Theorem 1.1 says "no A_3 or B_3 subdiagram; in other words, no subset {x,y,z} ...
  satisfies xyx=yxy, xz=zx, (y,z)_n=(z,y)_n with n=3 or 4".
- **Literal reading.** Taken at face value, the relation `(y,z)_n = (z,y)_n` with `n = 4`
  also holds when `m_yz = 2`. This would exclude `A_2 × A_1` triples too, which is the
  conservative class.
- **Diagram reading.** The paper's own usage in its proofs, "(2,3,3) triangle (A_3
  subdiagram)" and "no (2,3,4)-triangles", supports the class with `m_yz ∈ {3,4}`.
- **Resolution.** I imported only the conservative class. It satisfies the hypothesis
  under both readings, and the check is written in the route. The census reports both
  counts. Under the diagram reading, 13 of the 92 rank-4 classes with labels `≤ 5`
  leave the gap, `[3,5,3]` among them.

## Approaches and where each dies

1. **Import classes one at a time.** This gives items 3–5 above. It stops at the refined
   gap.
2. **Use the K(π,1) conjecture.** This dies because type F does not force a solvable
   word problem (`some-type-f-group-has-unsolvable-word-problem`). Godelle–Paris
   arXiv:1007.1365 Theorem 5.6 assumes K(π,1) and the free-of-infinity word problems, so
   it adds nothing here.
3. **Treat `A_Γ` as a colimit of its proper standard parabolic subgroups.** This holds
   for `|S| ≥ 3`, since every relation involves two generators.
   - It dies because I found no normal form theorem for such a colimit without
     curvature hypotheses on the Deligne complex, and the graph records those only for
     covered types.
   - Work of R. Charney on locally reducible Artin groups was not fetched. The reference
     and any word-problem consequence are unverified.
4. **Build an explicit finitely presented host of `AV_A`.** By the equivalence this is
   as hard as the problem itself, so it is not a reduction.
5. **Extend the BCHMR rewriting system.** This dies at `B_3` triples. The paper's example
   "n_atleast5" shows the exclusion is necessary for its algorithm, and the condition
   `m_bc ≥ 5` is built into Definition P3G.
6. **Use the Haettel–Huang gluing theorem (Theorem F).** For a free-of-infinity graph the
   presentation graph is complete. The theorem then yields only (cyclic type) ×
   (spherical type), which is already covered.
7. **Embed an uncovered group into a covered one**, for example through
   LCM-homomorphisms. This is an idea only; no uncovered group was mapped.
8. **Reconstruct the membership algorithm myself.** I sketched a right action of `A` on
   `A_T × {minimal coset representatives}`, driven by Deodhar's lemma: when `us` is not
   minimal, `us = tu` for some `t ∈ T`.
   - The braid relations would be checked in rank-2 residues, through the set of
     `x ∈ {s,t}` with `w_0 x w_0^{-1} ∈ T`.
   - This is meant to be the retraction `π_T` of Godelle–Paris. The sketch was not
     completed or checked, and nothing in the graph depends on it. The route cites
     Theorem 3.5 instead.

## Items for others

- The gap line in `every-artin-group-has-solvable-word-problem` ("rank at least 4, not
  FC type, not 2-dimensional, not euclidean, and some label equal to 3") is now out of
  date.
  - The sharper gap is the one above, applied to the connected Dynkin components of the
    maximal free-of-infinity subgraphs.
  - I did not edit that committed node. The information is in
    `every-free-of-infinity-artin-group-has-solvable-wp`.
- The imported proofs I did not read are the natural referee targets:
  - BCHMR Theorem 1.1;
  - HH Theorem E and the Mosher reference behind Theorem D;
  - GP Lemma 2.6 and `π_T`;
  - Serre's normal form theorem.

## Literature consulted (all accessed 2026-09-16 through export.arxiv.org)

- **Read in part, from the LaTeX source:**
  - E. Godelle, L. Paris, *Basic questions on Artin-Tits groups*, arXiv:1105.1048v1
    (2011-05-05): Theorems 3.3 and 3.5 (statements), Corollary 3.4 (statement and
    proof), Theorem C and its proof.
  - E. Godelle, L. Paris, *K(π,1) and word problems for infinite type Artin-Tits groups,
    and applications to virtual braid groups*, arXiv:1007.1365v1: Proposition 2.7 with
    proof, and the statement of Theorem 5.6.
  - J. Gálvez Mateos, F. Gavazzi, L. Paris, *Parabolic subgroups and word problem in
    virtual Artin groups*, arXiv:2602.23819v1 (2026-02-27): Propositions 2.13 and 2.18
    (statements only), Theorem 1.4.
  - R. Blasco-García, M. Cumplido, D. F. Holt, R. Morris-Wright, S. Rees, *Rewriting in
    Artin groups without A_3 or B_3 subdiagrams*, arXiv:2412.12195v2: Theorem 1.1, the
    detailed theorem, and Example n_atleast5 with the remarks citing it.
  - T. Haettel, J. Huang, *New Garside structures and applications to Artin groups*,
    arXiv:2305.11622v2: introduction, Theorems D, E and F, and the definition of cyclic
    type.
- **Abstracts only:** arXiv:2109.07891, arXiv:2204.03523, arXiv:2507.16770,
  arXiv:2310.14632, arXiv:2606.13296, arXiv:1606.08995.
- **Not fetched, unverified:** R. Charney's work on locally reducible Artin groups (exact
  reference not checked); J.-P. Serre, *Trees*; H. van der Lek's thesis (quoted only
  through the survey).

## Referee (2026-09-16)

**What was checked.**
- Every file in the lane was read in full: the ten `research/` nodes, this note, and the
  census script with both outputs. The existing nodes they cite were read too:
  - `every-artin-group-has-solvable-word-problem`;
  - `known-artin-classes-have-solvable-word-problem` and its citation;
  - `self-twisted-bt-group-fp-embedding-iff-solvable-wp`;
  - `known-type-artin-twisted-bt-groups-embed-in-fp-groups` and its proof;
  - the root claim.
  No unlisted solver files were found.
- **Sources.** The LaTeX sources of arXiv:1105.1048v1, arXiv:1007.1365v1,
  arXiv:2412.12195v2 and arXiv:2305.11622v2 were downloaded again.
  - The quoted statements were compared with the sources: Godelle–Paris Corollary 3.4,
    Theorems 3.5 and C, and Proposition 2.7; BCHMR Theorem 1.1 and Example n_atleast5;
    Haettel–Huang Theorems D, E and F and the definition of cyclic type.
  - The theorem letters were confirmed from the `mthm` environments. Theorem E has label
    `thm:main1` and Theorem F has label `thm:intro garside`.
  - No fabricated citation or misquotation was found.
- **Mathematics.**
  - Rerunning the single-graph induction `P(n)` gives the reduction to maximal
    free-of-infinity subsets.
  - The product lemma proof is complete.
  - The check that the conservative class satisfies the BCHMR hypothesis under both
    readings is correct, including the order of `st` in `W`.
  - The assembly route requires only nodes that exist, and it adds no `requires: []`
    route into the root.
- **Census.** The script was rerun with labels 5 and 6. Both outputs were reproduced
  exactly: 276/79/92 and 900/172/209, smallest nonzero eigenvalue `5.478e-3`.
  - The class counts 276 and 900 agree with an independent Burnside count over `S_4`
    acting on the six edges.
  - The cross-check lists match the classical ones:
    - 5 irreducible spherical rank-4 classes (`A_4, B_4, D_4, F_4, H_4`);
    - 3 irreducible affine classes (`Ã_3, B̃_3, C̃_3`);
    - 9 compact hyperbolic tetrahedra;
    - 5 Lannér 4-simplices.
- **Duplicates.** The research tree was searched, and no existing node states the
  Godelle–Paris reduction, the BCHMR class or the cyclic-type class.

**What changed.**
1. **Example in `artin-wp-from-covered-maximal-free-of-infinity-subgraphs`.** It is
   covered by an earlier result. Two `(3,3,3,4)` 4-cycles glued at a vertex appear to
   satisfy the hypotheses of Haettel–Huang Theorem F, which already gives a Garside
   structure on `A_Γ × Z`. So that example is new only relative to the graph, and item 4
   above overstates it.
   - A referee remark was added with the check.
   - A second example was added that no single imported theorem covers. It is a
     `(3,3,3,4)` 4-cycle and a `[5,3,5]` path sharing one vertex, with `∞` on the
     cross pairs. The `A_3` triple rules out BCHMR, and the `[5,3,5]` complete subgraph
     rules out Theorem F.
2. **Heading in `every-free-of-infinity-artin-group-has-solvable-wp`.** "Where the open
   cases are" was renamed "Cases the graph does not yet cover". The gap is relative to
   the graph and the literature consulted. The heading should not suggest that no
   algorithm is known elsewhere.
3. **Census script docstring.** "Theorem main1" was changed to "Theorem E, source label
   thm:main1". The outputs are unaffected.

**Verdict.** Sound. Landed with fixes; nothing was downgraded or withdrawn.
- **Outcome for the hole.** This is a reduction, not a solution.
  `every-artin-group-has-solvable-word-problem` is equivalent to the new hole
  `every-free-of-infinity-artin-group-has-solvable-wp`, which stays open.
- **Outdated gap line.** The gap line in the committed
  `every-artin-group-has-solvable-word-problem` is out of date. It was not edited,
  following the rule against editing committed nodes that one did not create.

**Remaining trust surface.** These were imported, not checked:
- the proofs of Godelle–Paris Lemma 2.6 and the retraction `π_T`;
- Serre's normal form theorem for amalgams;
- van der Lek injectivity, quoted through the survey;
- the proofs in BCHMR;
- Haettel–Huang Proposition `prop_cyclic`, Theorem `thm_main`, and the Mosher reference
  behind Theorem D.
