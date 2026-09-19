# Finite pair-graph check for a hyperbolic Kazhdan group: feasibility verdict (bh-q12-kazhdan, 2026-09-19)

**Verdict: not run.** A brute-force pair-graph computation for the smallest explicit hyperbolic Kazhdan group we found
cannot reach depths that carry information about its boundary within the approved envelope
(`taskset -c 30,31 nice -n 19 timeout 900` on acn112). No script was run and no logs exist. The surface-type
calibration already exists: `gq-bh-finf-hyp-cone-matching-test.md`, the right-angled pentagon, with 4
non-branching singular chains per generator, matching Theorem D of `bbmz-singularity-is-a-recurrent-coincidence`.

## The criterion any future check must use

`sing(g)` is uncountable iff some type in `T_sing`, reachable from a level-`|g|` root type, lies in a
**nontrivial** strongly connected component of the pair graph `𝒢_g` that is not a single simple cycle, counting
parallel edges. This is the form corrected by bh-ref-q12 (5af33a077b, landed b96c8ebd41).

## The chosen group

Caprace–Conder–Kaluba–Witzel, *Hyperbolic generalized triangle groups, property (T) and finite simple quotients*,
arXiv:2011.09276, Theorem 1.2. It was read in the arXiv source (`SmallHyp.tex`, fetched to
`/projects/standard/hsiehph/sauer354/bh-q12-kazhdan/cckw/`).

`𝓗_31 = ⟨a, b, c | a^5, b^5, c^5, [a,c], [b,c,b], [b,c,c,b], [b,c,c,c], a b a^2 b a^2 b a b^{-1} a b^{-1},
b^2 a b a^{-1} b a^{-1} b a b^2 a, (b a b^{-1} a b a^{-1})^2⟩`

- **Conventions** (source). `[x,y] = x^{-1}y^{-1}xy`, and `[x_1, …, x_n] = [[[x_1,x_2], …], x_n]`.
- **Status** (source, Theorem 1.2). It is "an infinite hyperbolic 5-fold generalized triangle group satisfying
  Kazhdan's property (T)".
- **Vertex groups** (source). `⟨a,b⟩ ≅ PSL_2(31)`, `⟨c,a⟩ ≅ C_5 × C_5`, and `⟨b,c⟩` is a 5-Sylow subgroup of
  `Sp_4(5)`.
- **Geometry** (source). The link girths are 10, 8 and 4. The group acts geometrically on a CAT(−1) triangle
  complex with angles `π/5, π/4, π/2`, which gives hyperbolicity.
- **Property (T)** (source). It uses the Ershov–Jaikin-Zapirain criterion, with a computer-certified spectral gap
  estimate for the link of `⟨a,b⟩`.
- **Why this group.** Its presentation is among the shortest known for hyperbolic Kazhdan groups, since the paper
  says its examples are shorter than the previously known shortest ones. `𝓗_109`, from the same theorem, is
  larger.

## Why a run would carry no signal

1. **Cost of exact atoms.** Exact horofunction atoms need `d(z, b) = |b^{-1} z|` for every `z` in a window of spheres
   `S_{R−1..R+1}` and every `b` in the ball `B_M`. Each value is a word reduction through an automatic structure
   (KBMAG). That is about `|S_R| · |B_M|` reductions, which caps a 15-minute two-core run at roughly `R ≤ 8` and
   `M ≤ 4`.
2. **Scale of one vertex group.** `|PSL_2(31)| = 14880`.
   - In its own generators `a^{±1}, b^{±1}` (both of order 5), the `r`-ball has at most `2·3^r − 1` elements. So its
     diameter is at least 9.
   - In the word metric of `𝓗_31` (6 letters, each generator of order 5), the `r`-ball has at most
     `1 + 6(5^r − 1)/4` elements, which is below 14880 for `r = 5`. So some element of `⟨a,b⟩` has length at least 6.
3. **Consequence.** Every feasible level (`n ≤ 4`, window `R ≤ 8`) lies at the scale of a single `PSL_2(31)`
   vertex star.
   - The atoms and pair types seen there are governed by the finite group's Cayley graph, not by `∂𝓗_31`.
   - Theorem E's proven window radius is of order `8δ + O(|g|)`, far larger still.
   - So a run could not detect a reachable nontrivial non-cycle component in `T_sing`, or rule one out. We did not
     spend the compute, and no calibration run was needed.
4. **No change of generators helps.** Adding generators, for example all nontrivial edge-group elements (which makes
   the Cayley graph the chamber graph of the triangle complex), raises the growth rate. The other explicit
   hyperbolic Kazhdan groups known to us (larger `p`-fold families, Sp(n,1) lattices, Żuk groups) are larger.

## What would decide it

- **A structural analogue of Theorem D for generalized triangle groups.** Take the generating set to be the nontrivial
  edge-group elements, so the Cayley graph is the chamber graph of the CAT(−1) triangle complex.
  - Singularity should then be a coincidence condition on events in the three vertex links: the coset graphs of
    girth 10, 8 and 4 for `𝓗_31`.
  - That is decidable by hand from finite coset-graph data, with no ball enumeration.
  - This is the recommended next step for Conjecture U.
- **A cheap cubulated control.** The right-angled Coxeter group on the Petersen graph is hyperbolic, since the graph
  is triangle-free with girth 5. Its boundary is expected to be the Menger curve with no local cut points (recalled
  from the literature on right-angled Coxeter groups with Menger boundary; not checked). Its wall stabilizers
  `C_2 × (C_2 ∗ C_2 ∗ C_2)` have Cantor limit sets.
  - Theorem D applies to it exactly.
  - So "no local cut points" versus "uncountable singular set" can be tested by hand in the cubulated world. This is
    not done here.
