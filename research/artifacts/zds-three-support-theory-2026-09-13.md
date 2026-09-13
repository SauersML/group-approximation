# Support-3 zero divisors: theory lane (2026-09-13)

Lane `solve-zds-three-support-theory`. Target: `kaplansky-zero-divisor-conjecture`, case
`|supp alpha| = 3`. The aim was to move from exhaustive search toward proofs. Computation ran on
MSI. The files are in `research/artifacts/zds-three-support-theory-2026-09-13/`.

## 1. Sources read at source (arXiv TeX fetched on MSI)

- **Abdollahi--Taheri, arXiv:1612.00934** (`main.tex`).
  - Lemma `supp`: after translation `G = <supp alpha>` for least `beta`.
  - Thm `thm-graph`: Schweitzer Thm 4.2, connected simple cubic triangle-free over `F_2`.
  - Thm `K3-K3`, Thm `C4-1` (36 classes of 4-cycle relations, 9 not excluded), Thm `C4`
    (a 4-cycle gives `x^2 = y^3`).
  - Table `tab-C5` (105 classes, 35 starred) and its appendix items, Table `tab-C6` (351 classes).
  - Thm `T2` and Cor `maincor` (`>= 20` over `F_2`).
- **Schweitzer, arXiv:1202.6645** (`zero_divisors.tex`): Thm `thm:length:2`, Thm `thm:bsg:groups`
  (quotients of `BS(1,n)` satisfy the conjecture over `F_2`), and the 3 x m cubic-graph reduction.
- **Steenbock, arXiv:1307.0981**, introduction: "Do Rips-Segev groups satisfy Kaplansky's
  zero-divisor conjecture?"
- **Arzhantseva--Steenbock, arXiv:1407.2441**.
  - Thm `main`: every finitely presented `Q` is a quotient of a torsion-free hyperbolic group
    without unique products.
  - Cor `C: T`: torsion-free hyperbolic Property (T) groups without unique products.
  - The introduction states that Steenbock proved the generalized Rips--Segev groups hyperbolic,
    and that the Passman, Promislow and Carter groups are a-T-menable.
- **arXiv:2501.07646** (taikos, left alignment): no counterexamples of type `(m,n)` for `m <= 5`,
  or for `m, n <= 13` by computer. That is conditioned on the product-structure conditions
  `T_1`--`T_4` of Mineyev 2024, a geometric class, not the general case.
- **arXiv:2607.19687** (Nielsen--Soelberg landscape): abstract only.

## 2. Directive step (c) is void

The Promislow group `P` is torsion-free and virtually `Z^3`, hence elementary amenable. So `k[P]`
is a domain for every field (Kropholler--Linnell--Moody), as the root node and
`zero-divisor-search-2026-09-12.md` §2 already record. No search was run on `P`.

## 3. Landed claims

| id | status | content |
|---|---|---|
| `zero-divisor-support-vertex-cones-contain-positive-relations` | established | at each support point the left differences multiply to 1 along a positive word with two letters; cone/dynamical exclusion criterion |
| `kaplansky-graph-squares-force-central-trefoil-generators` | established | a 4-cycle makes `<supp alpha>` a torsion-free central extension of an infinite quotient of `PSL(2,Z)` with `b_2 >= 1` |
| `cyclic-centralizer-hosts-have-square-free-kaplansky-graphs` | established | hosts with cyclic centralizers (torsion-free hyperbolic): no cycles of length at most 4 |
| `cyclic-centralizer-host-pentagons-have-two-relation-orbits` | established | in those hosts 5-cycles read one of two relators up to automorphism |
| `abdollahi-taheri-pentagon-relations-73-and-77-are-trefoil-type` | established | A--T rows (73), (77) are starred with a faulty Tietze computation; both define the trefoil group |
| `cyclic-centralizer-groups-have-no-support-three-zero-divisors` | open | the host-class target, with attempts |

## 4. Census of cycle relations

`cycle_relators.py` (md5 `b52f901859bf18fb09157718e96ffe69`) enumerates the `2k`-tuples of a
`k`-cycle with consecutive entries distinct cyclically, and groups them under rotation and
reversal. For each relator `prod a_i^-1 b_i` it runs a breadth-first search over elementary
Nielsen moves, conjugation moves and signed letter permutations, bounded by length plus 4 and at
most 60000 words. It then matches the least forms against these patterns:
- **A:** primitive, or a power of a primitive element;
- **S:** `BS(1, j)` or `p^2 q^(+-2)`;
- **C:** `p^a q^b` with `|a|, |b| >= 2`, not `(2,2)`;
- **B:** `BS(m, n)` with `|m|, |n| >= 2`;
- **G:** anything else.

| cycle length | tuples | classes | A | S | C | B | G |
|---|---|---|---|---|---|---|---|
| 2 | 18 | 6 | 6 | 0 | 0 | 0 | 0 |
| 3 | 66 | 13 | 9 | 4 | 0 | 0 | 0 |
| 4 | 258 | 36 | 12 | 15 | 9 (3,2) | 0 | 0 |
| 5 | 1026 | 105 | 15 | 18 | 30: (3,2) x15, (4,2) x12, (3,3) x3 | 6: (2,2) x3, (-2,2) x3 | 36 |
| 6 | 4098 | 351 | 18 | 40 | 48: (3,2) x12, (4,2) x6, (5,2) x15, (3,3) x9, (4,3) x6 | 12: (2,3) x6, (-2,3) x6 | 233 |

- **Outputs.**
  - `census2345.out` (md5 `37a3c10dd8479824fbc4e9294a655f6a`) and `cycle_relators.json`
    (md5 `f48e920d28e0f40436aeedae53b13c4d`): lengths 2--5, run on the MSI login node.
  - `census6.out` (md5 `4c69960826dc748d4b9aef3ccfbb5ed0`) and `cycle_relators6.json`
    (md5 `b0950aaf7c9b6763b6e38c48d9cb8896`): length 6, slurm job 716561 (`c6.sbatch`, log
    `c6.716561.log`).
- **The 5-cycle G classes.** Their least forms are `h_3^-2 h_2^-2 h_3 h_2` and
  `h_3^-2 h_2^-1 h_3^-1 h_2^2`, up to rotation, inversion and signed letter permutation.
- **Scope.** The search is not claimed complete for Whitehead equivalence. A class labelled G may
  still be equivalent to a pattern. Every A, S, C and B label comes from an explicit automorphism
  image, so those labels are certified.

**Cross-checks against A--T.**
- `check_at_tables.py`, output `check_at_tables.out`, ALLOK.
  - The nine C classes at length 4 are exactly A--T rows 5, 7, 14, 17, 21, 22, 25, 26, 29.
  - Each A--T substitution `x^2 y^-3` is conjugate to the row relator in `F(h_2, h_3)`.
- `at_c5_parse.py`, output `at_c5_parse.out`.
  - All 105 rows of `tab-C5` match a census class.
  - Starred rows: 15 A, 18 S, and 2 C, namely rows 73 and 77. Unstarred rows: 28 C, 6 B, 36 G.
- `torus_witness.py`, output `torus_witness.out`.
  - `h_3 -> h_3 h_2^2` sends (73) to `h_3^-3 h_2^-2`, and `h_2 -> h_2 h_3^2` sends (77) to
    `h_2^3 h_3^2`.
  - The displayed A--T Tietze step for (73) is wrong: `h_3 -> h_2 h_3` gives
    `h_2 h_3^-1 h_2^-1 h_3^-1 h_2 h_3^-1`.

## 5. Consequence for the landed support bound

`f2-support-three-zero-divisors-need-support-at-least-22-proof` step (2) cites A--T Cor 6.2 for
`n >= 20`. That corollary uses 44 forbidden subgraphs, and the appendix that details them opens
with the tables of 5-, 6- and 7-cycle relations, with starred rows treated as contradictions. If
some forbidden subgraph needs row 73 or 77, the paper's proof of `>= 20` has a gap. Whether any
does was not checked.
The repository's own runs `ladder.595297` and `n18.595304` exclude every graph with at most 18
vertices using only Schweitzer Thm 4.2. So the bound stands, but step (2) should cite those runs.
That node belongs to the zero-divisor search lanes, which touched it within 6 h, so it was not
edited.

## 6. Structural facts proved in the lane but not landed as claims (F_2, `alpha = 1 + x + y`)

- **Two expressions.** Every product in `S = AB` has exactly two expressions. So
  `|B ∩ xB| = |B ∩ yB| = |xB ∩ yB| = n/2`, and the three sets partition `S`.
- **Lines.** For each `u in {x, y, x^-1 y}`, `B` is a disjoint union of exactly `n/2` maximal
  `u`-lines, which have average length 2.
  - Every point is exactly one of an `x`-start and a `y`-start.
  - The `x^-1 y`-starts are the points that are not `x`-ends.
- **Rotation surface.** With the rotation `(1, x, y)` at every vertex, the Kaplansky graph embeds
  in a closed orientable surface.
  - Its faces are cyclic sequences of whole lines of types `x`, `y`, `x^-1 y`.
  - The number of faces is at most `n/2`, so the genus is at least 1.
  - The opposite rotation gives the mirror surface.

These add no sieve beyond coset coincidence, so they were not landed.

## 7. Exact gap

- **General hosts.** Kaplansky for `|supp alpha| = 3` stays open. Local cycle relations stop
  excluding at length 5 (36 of 105 classes unrecognized) and length 6 (233 of 351).
- **Hosts with cyclic centralizers,** which include all hyperbolic groups without unique products:
  exclude a girth-5 cubic Kaplansky graph whose 5-cycles read the two remaining relators.
