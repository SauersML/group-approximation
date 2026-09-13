# Zero-divisor supports beyond the published bounds (2026-09-12)

Lane `zero-divisor-search`. Target: `kaplansky-zero-divisor-conjecture`. Every published bound
and every structural fact below was read from the paper's PDF. All computation for this lane
runs on MSI.

## 1. Coverage already in the repository (main at `11c6d1a50`)

| node or artifact | group | coefficients | content |
|---|---|---|---|
| `e33-balls-have-no-small-zero-divisors` | `E_3(3) <= SL_3(Z)` | `F_2`, `F_3`, `Q` | SAT census in radius-two balls (runs `e33-p2-r22`, `e33-p3-r22`, `e33-p2-r23`) |
| `e33-no-unique-product-pairs-of-small-radius` | `E_3(3)` | every field | no pair without unique products with radii at most `(3,3)`, or radii `(2,4)` or `(4,2)` |
| root node, Attempts | `E_3(3)` | characteristic 0 and 3 | not a host (congruence-kernel constraint) |
| `zero-divisor-support-subgroup-host-constraints` | any torsion-free | every field | host is finitely generated, not UP, not elementary amenable (EA); in characteristic 0 it violates Strong Atiyah |
| `zero-divisor-host-is-not-virtually-compact-special`, `fisher-sanchez-peralta-special-and-3-manifold-domains` | any torsion-free | every field | host is not virtually compact special and not a 3-manifold group |
| `fixed-tester-finite-field-group-rings-are-domains` | the fixed torsion-free tester | finite fields | domain |
| `promislow-radius4-one-sided-and-integral-separation` | Promislow `P` | `F_2` | unit census, not zero divisors |
| `minimal-five-seven-partner-cannot-escape-support-subgroup` | any group | `F_2` | inverse pairs, not zero divisors |
| `kaplansky-df-sat-search-2026-09-12`, `kaplansky-collision-partner-search-2026-09-12` | `L_(F_2)(1,2)^x` | `F_2` | direct finiteness |
| `crossed-product-zero-divisor-filters-2026-09-12` | odd-measure crossed product | `F_2` | Cohn-family witnesses, not group rings of torsion-free groups |

None of these gives a support-size bound over an arbitrary torsion-free group. Those bounds come
only from the literature in §3.

## 2. Hosts excluded before any search

* **The Promislow group.** `P = F(2,6)` (DLNV = Dietrich--Lee--Nies--Vinyals, arXiv:2603.22640,
  §4 fact (3)). It is torsion-free and virtually `Z^3`, hence EA. By Kropholler--Linnell--Moody
  (KLM), `k[P]` is a domain for every field `k`, as the root node records. So route (a) of the lane
  brief, zero divisors in `F_2[P]` or `F_p[P]`, is void by theorem. No search was run on `P`.
* **The Fibonacci groups `H_n = F(n-1,n)`.** For even `n >= 4` these are torsion-free 3-manifold
  groups whose group rings over any domain have no zero divisors (DLNV §4.1). `H_4` is a torsion-free
  polycyclic group (DLNV Prop 5.1).
* **The Nielsen--Soelberg groups `G_1`, `G_2`, `G_3`** (N--S (3.1), (3.5), (4.2)). All three are
  torsion-free (N--S) and virtually polycyclic. So `K[G_i]` is a domain for every field `K`, by
  Farkas--Snider in characteristic 0, Cliff in characteristic `p`, or KLM. Through the fraction
  field, `R[G_i]` is a domain for every commutative domain `R`. N--S end §4 with: "We leave it as
  an open question whether or not any of the three group rings `R[G_i]`, for `i in {1,2,3}`, is a
  domain", where `R` is a domain. Nothing here decides a noncommutative `R`.
  - `G_1`: N--S (3.2) already shows that the index-32 normal subgroup `H` is `Z` times a
    torsion-free class-2 nilpotent group. GAP reproduces this (§6).
  - `G_2`: `H = <a_1^2, a_3^2, a_6^2, a_1 a_3 a_6^-1>` has index 4 and is normal (GAP, §6). Its
    Reidemeister--Schreier presentation on these generators `h_1, ..., h_4` says: `h_1` and `h_2`
    are central, and `h_3^-1 h_4^-1 h_3 h_4 = h_2^2 h_1^-2`. With `u = h_1 h_2^-1`,
    `H = <h_2> x <u, h_3, h_4 | u central, [h_3, h_4] = u^-2>`. This is `Z` times a torsion-free
    class-2 nilpotent group.
  - `G_3 = <x,y | (yx)^2 (xy)^2, (xy^-1)^2 (xy)^2>`, by hand. Put `t = (xy)^2`. The first relator
    says `(yx)^2 = t^-1`, and `(yx)^2 = x^-1 t x = y t y^-1`, so `x` and `y` invert `t` and `<t>` is
    normal. In `Q = G_3/<t> = <x,y | (xy)^2, (xy^-1)^2>` we have `yxy = x^-1` and
    `y^-1 x y^-1 = x^-1`, so `y x^2 y^-1 = (yxy)(y^-1 x y^-1) = x^-2` and `<x^2>` is normal in `Q`.
    Then `Q/<x^2> = <x,y | x^2, xyx = y^-1>`, the infinite dihedral group. So `G_3` has a normal
    series with cyclic factors: it is polycyclic, of Hirsch length at most 3. GAP gives
    `[G_3 : H] = 8` with `H` normal and `H^ab = Z^2 x Z/8` (§6).

## 3. Published frontier (read from the PDFs)

A zero divisor `alpha beta = 0` over a domain has `supp alpha * supp beta` without unique
products. So non-UP bounds are zero-divisor bounds.

| `|supp alpha|` | bound on `|supp beta|` | coefficients | source |
|---|---|---|---|
| 3 | `>= 19` | any domain | Nielsen--Soelberg, Thm 1.4 |
| 4 | `>= 14` | any domain | N--S Thm 1.4 |
| 5 | `>= 11` | any domain | N--S Thm 1.4 |
| 6 | `>= 10` | any domain | N--S Thm 1.4 |
| 7 | `>= 9` | any domain | N--S Thm 1.4 |
| any | `|supp alpha| + |supp beta| >= 16` | any domain | N--S Thm 1.4 |
| `alpha^2 = 0` | `|supp alpha| >= 8`; sharp for `A^2` non-UP | any domain | N--S Thm 1.2 |
| 3 | `>= 20` | `F_2` | Abdollahi--Taheri, Thm 6.1 and Cor 6.2 |
| 4 | `>= 9` | `F_2` | Abdollahi--Jafari, arXiv:1709.08204 (superseded) |
| 3 | `>= 12` | any field | Abdollahi--Jafari, arXiv:1808.08708 (superseded) |
| 3, 4 | `> 16`, `> 7` | `Q` | Schweitzer, arXiv:1202.6645 (superseded) |

Sources: N--S = P. P. Nielsen and C. Soelberg, *Small sets without unique products*, J. Algebra
Appl. 23 (2024) 2550050 (preprint `mathdept.byu.edu/~pace/KaplanskyConjecture_web.pdf`).
A--T = arXiv:1612.00934.

**Methods and costs.**
- *N--S.* Magma search over the universal groups
  `G_X = <a_i, b_j | a_i b_j = a_k b_l for (i,j,k,l) in X>` with `a_1 = b_1 = 1`. Patterns `X` are
  extended one quadruple at a time, with reductions under `S_m x S_n`, and a pattern is rejected
  when it forces "simple" torsion (orders at most 100 were tested). The search for Thm 1.2 ran one
  year on a personal computer (`n <= 7`), then one year on BYU's Mary Lou supercomputer (`n = 8`,
  not exhaustive). Thm 1.4 took a four-year computation on BYU supercomputers.
  The two survivors are `G_1` and `G_2`. §4 shows they share one two-set pattern, realized by
  `G_3 = <x,y | (yx)^2(xy)^2 = (xy^-1)^2(xy)^2 = 1>`.
- *Schweitzer.* Matched rectangles, pruned by cyclic closure in a core subgroup, periodic cycles,
  and mismatching parallel sequences. The unpruned rectangles are resolved in GAP. Figure 8, on
  Xeon E5620 cores:

  | `|supp alpha|` × `|supp beta|` | 3 × 10 | 3 × 12 | 3 × 14 | 3 × 16 | 4 × 6 | 7 × 4 |
  |---|---|---|---|---|---|---|
  | time | 4 s | 34 s | 1877 s | 111657 s | 436 s | 17570 s |

  At 3 × 16, 4068 rectangles went to GAP. The step from 14 to 16 grows about 59 times. If that
  rate held, 3 × 20 would take about `4e8` s.
- *A--T, `F_2` and `|supp alpha| = 3`.* The Kaplansky graph on `supp beta` is connected, simple,
  cubic and triangle-free (Thm 2.9). The paper has 44 forbidden subgraphs, and the families `L_n`
  and `M_n` (Thm 4.5) are also excluded. Table 3 counts connected cubic triangle-free graphs:

  | `n` | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 |
  |---|---|---|---|---|---|---|---|---|---|
  | graphs | 0 | 1 | 2 | 6 | 22 | 110 | 792 | 7805 | 97546 |

  All of them are excluded for `n <= 18`. **1120 graphs remain at `n = 20`** (Thm 6.1).

**First open cases.**
- Over `F_2` with `|supp alpha| = 3`: `|supp beta| = 20`, the 1120 graphs.
- Over any domain: `(3,19)`, `(4,14)`, `(5,11)`, `(6,10)`, `(7,9)`.
- `alpha^2 = 0` with `|supp alpha| = 8`, in a host that is not EA.

Tabei (arXiv:2607.18346) works only inside `P`, which is EA.

## 4. Theorem: a small left support has no orderable quotient

**Theorem.** Let `G` be torsion-free, and let `A, B` be finite nonempty subsets such that no
element of `AB` has a unique expression `ab`. Assume `1 in A` and put `H = <A>`. Let
`phi: H -> L` be a homomorphism to a left-ordered group. Then the minimum of `phi(A)` is attained
at no fewer than three elements of `A`, and so is the maximum. Hence:
1. if `phi` is not constant on `A`, then `|A| >= 6`. When `|A| = 6` the fibre sizes are 3+3;
   when `|A| = 7` they are 3+4, 4+3 or 3+1+3;
2. if `|A| <= 5`, then `H` has no nontrivial left-orderable quotient. So `H^ab` is finite, every
   homomorphism from `H` to `Z`, to a free group, to a torsion-free nilpotent group or to
   `Homeo^+(R)` is trivial, and `H` is not locally indicable;
3. if `1 in B` and `|B| <= 5`, the same holds for `<B>`.

**Proof.** Fix `a in A` with `phi(a)` minimal. For each `b in B` the product `ab` has a second
expression `ab = c b'`. Here `c != a`, since `c = a` forces `b' = b`. Choose one such `c = c(b)`
and put `p(b) = b' = c^-1 a b`. Iterating `p: B -> B` from any point reaches a cycle
`b_0, b_1 = p(b_0), ..., b_k = b_0` with `k >= 1`. With `c_i = c(b_i)` and `u_i = c_i^-1 a`,

```text
u_(k-1) ... u_1 u_0 = b_k b_0^-1 = 1   in H.                                   (*)
```

(i) If every `c_i` equals one element `c`, then `(c^-1 a)^k = 1` with `c^-1 a != 1`, which is
torsion. So at least two distinct elements `c_i` occur.

(ii) Since `phi(a) <= phi(c_i)`, left invariance gives `phi(u_i) = phi(c_i)^-1 phi(a) <= 1`. Put
`w_i = phi(u_(k-1) ... u_i)`. Then `w_i = w_(i+1) phi(u_i) <= w_(i+1)`, strictly when
`phi(u_i) < 1`, and `w_(k-1) = phi(u_(k-1)) <= 1`. So `w_0 <= 1`, with equality only if every
`phi(u_i) = 1`. Since `w_0 = 1` by `(*)`, `phi(c_i) = phi(a)` for all `i`.

So the fibre of the minimum contains `a` and at least two further elements. The maximum is
symmetric, using the reversed order. If `phi` is not constant on `A`, the two fibres are disjoint,
so `|A| >= 6`, and the listed splits are the only ones. If `|A| <= 5`, then `phi` is constant on
`A`, so `phi(A) = {phi(1)} = {1}` and `phi(H) = 1`.

For 2: `Z`, free groups, torsion-free nilpotent groups and subgroups of `Homeo^+(R)` are
left-orderable. `H` is finitely generated, so infinite `H^ab` maps onto `Z`. `H != 1`, since
`A = {1}` makes every product unique. For 3: `(AB)^-1 = B^-1 A^-1` has the same multiplicities,
and `<B^-1> = <B>`. QED

**For zero divisors.** Take `alpha beta = 0` with `alpha, beta != 0` over a field and
`a_0 in supp alpha`. Put `A = a_0^-1 supp alpha`; then `H = <a^-1 c : a, c in supp alpha>` does
not depend on `a_0`. If `|supp alpha| <= 5`, `H` has no nontrivial left-orderable quotient. For
example, a support-3 zero divisor `r_1 g + r_2 g x + r_3 g y` needs `<x,y>` to have finite
abelianization and no nontrivial action on the line.

**Remarks.**
- *Sanity check.* With `L = H` and `phi` the identity the fibres are singletons. So the theorem
  contains the classical fact that left-orderable groups have unique products.
- *A sieve for complete patterns.* Let `X` be a complete coincidence pattern: every pair `(i,j)`
  has a partner in `X`. Put `G_X` as in N--S (2.1) with `a_1 = b_1 = 1`, and suppose `X` is
  realized in a torsion-free group with `A` and `B` injective. The relations `(*)` already hold in
  `G_X`. The two facts used outside `(*)`, `c != a` and `(c^-1 a)^k != 1`, hold in the realization,
  hence as statements about the indices. So the proof runs verbatim for every
  `phi: <A>_(G_X) -> L`. **If `|A| <= 5` and `<A> <= G_X` has a nontrivial left-orderable
  quotient, for instance `G_X -> Q` nonzero on some `a_i`, then `X` is not realizable.** This test
  is exact and cheap: the rank of the matrix of exponent sums. It does not apply to incomplete
  patterns in an incremental search, since completing a pattern passes to a quotient of `G_X`.
- *Novelty is not established.* The statement is not in N--S, Schweitzer, A--T, both A--J papers,
  DLNV or Tabei. It is not in the repository either: a grep of `research/` at `11c6d1a50` for
  "unique product" finds `agent-bloop-unique-product-quotient-obstruction`, which is a different
  statement. The wider literature was not searched.

## 5. `F_2` and `|supp alpha| = 3` as a folded graph (search model)

Left-translate so that `alpha = 1 + x + y` and put `beta = sum_(b in B) b` with `|B| = n`. Over
`F_2` every element of `S = AB` has exactly two expressions, since one or three give coefficient 1.
So `|S| = 3n/2`, `B <= S`, and `E = S \ B` has `n/2` elements. Let `Gamma` be the graph on `S`
with an `x`-edge `b -> xb` and a `y`-edge `b -> yb` for each `b in B`. Then:
- each vertex of `B` has in-degree exactly 1;
- each vertex of `E` has one incoming `x`-edge, one incoming `y`-edge, and no outgoing edges;
- there are no pure `x`-cycles (`x^k = 1`), and likewise for `y`.

Contracting each `E`-vertex to an edge recovers A--T's Kaplansky graph. Its edge-ends carry the
port labels `1, x, y`, with the two ends of an edge labelled differently. `Gamma` is connected,
with `3n/2` vertices and `2n` edges, so `pi_1(Gamma)` is free of rank `n/2 + 1`: 11 cycle words
at `n = 20`. Put `G_Gamma = <x,y | cycle words>`. A zero divisor with this labelled graph exists
exactly when some torsion-free quotient of `G_Gamma` is injective on the vertices.

**Sound sieves.** Each is exact and passes to every quotient, or is §4.
1. Coincidence: a partial Todd--Coxeter enumeration of `<x,y | cycle words so far>`, seeded with
   the product graph, with each seed coset tagged by its product. Merging two cosets with different
   tags is a contradiction. New cosets are defined only up to a limit. Every relation read off the
   table holds in each realization of each completion, so sieves 1, 2, 3 and 6 also prune partial
   labellings.
2. Roots: a closed path reading a proper power `w^k` forces `w = 1`. Add `w` and rescan.
3. `G_Gamma` finite, detected by a bounded coset enumeration.
4. `G_Gamma` EA (KLM).
5. Orderable quotient (§4, complete pattern, `|A| = 3`): exclude when the `2 x (n/2 + 1)` matrix of
   exponent sums of the cycle words has rank less than 2.
6. Powers: if the table shows `u^e = 1` for a reduced word `u` and some `e >= 2`, then `u = 1`,
   since the host is torsion-free. Add `u` and rescan.

## 6. Status

- Landed: §§1--5, and the virtual polycyclicity of `G_1`, `G_2`, `G_3` in §2.
- GAP evidence: `zero-divisor-search-2026-09-12-gap/ns-structure.g`, with output `ns-structure.out`
  and log `ns-structure.587004.log`. It ran as MSI slurm job 587004, on GAP 4.11.1 in the SageMath
  10.7 container. For each group the output gives the index of the N--S subgroup `H`, whether `H`
  is normal, the Reidemeister--Schreier presentation on the given generators, `H^ab`, and a
  Tietze-simplified presentation.
  - `G_1`: index 32, normal. `h_1` and `h_2` are central, and
    `h_3 h_2^-2 h_4^-1 h_2^-1 h_3^-1 h_2^-2 h_4 h_2^-3` is a relator, which with `h_2` central is
    N--S (3.2). `H^ab = Z^3 x Z/8`.
  - `G_2`: index 4, normal, with the presentation in §2. `H^ab = Z^3 x Z/2`.
  - `G_3`: index 8, normal, `H^ab = Z^2 x Z/8`. The structure in §2 is by hand and does not use
    this output.
- Folded-graph search over `F_2`, in `zero-divisor-search-2026-09-12-search/`. `zds.c` (md5
  `380fa4a27fecf56f29abae8d2117b724`) reads the output of `nauty-geng -c -t -d3 -D3 n`, the
  connected triangle-free cubic graphs. A component of a zero divisor is again one, and A--T reduce
  to simple triangle-free graphs, so these are the only graphs to check. The program searches port
  labellings depth-first, one vertex at a time. Vertex 0 gets the ports `1, x, y` in a fixed order;
  this loses nothing, because the `S_3` on port names comes from translating `alpha`. Partial
  labellings are pruned by sieves 1, 2 and 3, with at most 4000 cosets. Complete labellings are
  pruned by sieves 1, 2, 3, 5 and 6, with at most 64000 cosets. Sieve 6 tries words of length at
  most 4 and `e <= 8`. Sieve 4 is not implemented. A graph with no surviving labelling carries no
  zero divisor.
  - Soundness test (`testgen.g`, `test.sbatch`). The input is all 175 groups of order 6 to 40, plus
    `A_5`, `SL(2,5)`, `PSL(2,7)` and `S_5`, with sampled `x, y`. It gives 99158 components of
    solutions of `(1 + x + y) beta = 0` over `F_2`, each with at most 40 vertices. With sieves 2--6
    off, sieve 1 prunes no prefix of any of them, at coset limits 0 and 4000/64000. With the ports
    normalized at vertex 0, the DFS reaches every one. Runs `v2-t-c0`, `v2-t-c4000` and
    `v2-ctl-c4000` in `surv.591297.log`: 0 failures.
  - `n <= 14`. geng gives 1, 2, 6, 22 and 110 graphs for `n = 6..14`, as in A--T Table 3.
    - An earlier version without sieve 6 (md5 `9dbb1e544f837e983be08dfbaae73c35`, not landed; log
      `test.589526.log`) left no labelling for `n <= 12`. At `n = 14` it left 16, all on the graph
      ``M???FAW`agD_K_Q_?``.
    - GAP (`surv.g`, `surv14.gap.out`): each of the 16 groups `<x,y | cycle words>` has
      abelianization `Z/3 x Z/7`. Enumeration over the trivial subgroup exceeds 2,000,000 cosets.
      Up to conjugacy, the only proper subgroup of index at most 4 has index 3 and abelianization
      `(Z/7)^2`.
    - With sieve 6 at complete labellings, nothing survives (`v2-s14.out`: 110 graphs, 8,428,940
      nodes, 320 power relators). This reproduces A--T's case `n = 14` without their list of
      forbidden subgraphs.
  - Cost with this order. At `n = 14` the node count per graph has median 33,989 and maximum
    855,949. From `n = 10` to `n = 14` it grows 3.3 to 4.3 times per two vertices, which projects
    about 3400 core-hours at `n = 20` over all 97546 graphs.
- Vertex order (`zds3.c`, md5 `18a83240ff82d0bcdcdcd33c15780d72`). `zds.c` labels the vertices in
  BFS order. By default `zds3.c` labels next the vertex with the most labelled neighbours, lowest
  index first, and joins it to the spanning tree at its first labelled neighbour. It adds three
  options, each off by default:
  - `-probe D` picks the root with the fewest labellings of its first `D` vertices. Any vertex can
    be the root, since the `S_3` on port names acts on all vertices at once.
  - `-pwd D` runs sieve 6 on partial labellings with at most `D` vertices unlabelled.
  - `-bs K -bsd D` excludes a labelling with at most `D` vertices unlabelled when the table shows
    `a b a^-1 = b^j` with `|j| <= K`. Here `(a, b)` runs over 72 pairs: a letter with a letter of
    the other class, or with a two-letter word in both classes, in either order. Each pair is a
    basis of `F(x, y)`. So the host is a quotient of `BS(1, j)`, hence solvable, and KLM applies.
- Job `exp14.sbatch` (593423, log `exp14.593423.log`) ran at `n = 14`. No labelling survives in
  any run.
  - Soundness test as above, with the new order: 0 failures (`v3-t-c0`, `v3-t-c4000`, `v3-ctl`).
  - `-bfs`: 8,426,048 nodes, against 8,428,940 for `zds.c`, whose spanning tree differs slightly.
  - Default order: 571,963 nodes, 15 times fewer, with median 3,305 and maximum 18,413 per graph.
    It takes 20 s, or 6 s with at most 1000 cosets at partial labellings (572,425 nodes).
  - Root probes cost more than they save. `-probe 6` gives 354,598 search nodes plus 1,270,020
    probe nodes. `-bs 8 -bsd 3` prunes 599 labellings and `-pwd 3` prunes 1073; neither changes
    the node count by more than 1%.
- `n <= 18` with `zds3.c`: default order, at most 1000 cosets at partial labellings and 64000 at
  complete ones, sieve 6 with words of length at most 4 and `e <= 8`. No labelling survives, no
  run hits a limit, and every exit code is 0.
  - `ladder.sbatch` (job 595297, log `ladder.595297.log`). `n = 6, 8, 10` take 174, 1271 and
    7177 nodes.

    | `n` | graphs | nodes | median per graph | max per graph | seconds |
    |---|---|---|---|---|---|
    | 12 | 22 | 53,560 | 2,280 | 11,525 | 0 |
    | 14 | 110 | 572,425 | 3,305 | 18,744 | 7 |
    | 16 | 792 | 9,349,699 | 8,237 | 72,299 | 111 |

    At `n = 14` without sieve 6, 20 labellings survive. They include the 16 left by the earlier
    version.
  - `n18.sbatch` (array job 595304). The concatenated shard logs are `n18.595304.logs.txt`, the
    output of `agg.sh` is `n18.595304.agg.txt`, and the GRAPH and TOTAL lines are
    `r18.lines.txt.gz`. geng res/mod gives 32 shards and 7805 graphs, as in A--T Table 3, with no
    duplicates. The search takes 179,291,759 nodes, with median 11,271 and maximum 324,527 per
    graph, and 2304 core-seconds. It prunes 111,968,100 labellings by coincidence, 6,551,884 as
    finite, and 4 by sieve 6.
  - So the search reproduces A--T's bound `|supp beta| >= 20` for `|supp alpha| = 3` over `F_2`.
    It uses their reduction to simple triangle-free graphs, but no forbidden subgraphs.
- Cross-check at `n = 16` with `zds.c` in BFS order (`n16.sbatch`, job 592716, log
  `n16.592716.log`). It reproduces the node counts above for `n <= 14`, and at `n = 16` leaves no
  labelling on any of the 792 graphs. The search takes 262,754,713 nodes, with median 97,533 and
  maximum 6,152,089 per graph, and all exit codes are 0.
- Running on MSI: `n20.sbatch` (all graphs at `n = 20` in 128 shards, array job 595808). From
  `n = 14` to `n = 18` the node count per graph roughly doubles per two vertices, which projects
  about 16 core-hours at `n = 20`.
