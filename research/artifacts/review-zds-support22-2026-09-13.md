# Review: zero divisors over F_2 with support 3 need support at least 22 (2026-09-13)

Reviewer lane `review-zds22`. The reviewer did not write any of the reviewed material.

**Scope.** Commit 3b5232827, which lands the claim
`f2-support-three-zero-divisors-need-support-at-least-22` (ESTABLISHED, unreviewed) and its route
`f2-support-three-zero-divisors-need-support-at-least-22-proof`. The review also covers §§5–6 of
`research/artifacts/zero-divisor-search-2026-09-12.md` and the bundle in
`research/artifacts/zero-divisor-search-2026-09-12-search/`.

Each item gets a verdict: PASS, FAIL or NIT. Items waiting on MSI job 692041 are marked PENDING and are
filled in by a later landing.

## 1. Abdollahi–Taheri, read in the source: PASS

Source: arXiv:1612.00934, v1 (3 Dec 2016, the only version). Both the PDF and the TeX e-print were
fetched on MSI and run through `pdftotext -layout`. Quotes are from the PDF text.

- **Standing hypothesis, §2 p. 4.** "Throughout this paper let G be a torsion-free group and
  α = α1h1+α2h2+α3h3 ∈ F[G] such that |supp(α)| = 3. Suppose further that αβ = 0 for some non-zero
  β ∈ F[G] and assume that n := |supp(β)| is minimum with respect to the latter property".
- **Adjacency, §2.** "two vertices g_i and g_j are adjacent whenever h_{i′} g_i = h_{j′} g_j for some
  distinct i′, j′ ∈ {1, 2, 3}."
- **Theorem 2.9, pp. 7–8.** "(Theorem 4.2 of [19]). Any Kaplansky graph over F2 is a connected simple
  cubic one containing no subgraph isomorphic to a triangle." The proof says it is "essentially the same
  as the proof of [19, Theorem 4.2]", with connectedness coming "from the way we have chosen β of minimum
  support size". [19] is Schweitzer.
- **Opening of §6, p. 32.** "By Remark 4.2, the number of vertices of K(α, β) must be an even positive
  integer n ≥ 4."
- **Table 3, pp. 33–34.** "Existence of the forbidden subgraphs in non-isomorphic connected cubic
  triangle-free graphs with the size of vertex sets n ≤ 20". Row "Total" for n = 4, …, 20 reads
  0 1 2 6 22 110 792 7805 97546, and row "Remains" reads 1120 at n = 20.
- **Theorem 6.1, p. 34.** "The vertex set size of K(α, β) must be greater than or equal to 20.
  Furthermore, there are just 1120 graphs with vertex set size equal to 20 which may be isomorphic to
  K(α, β)."
- **Corollary 6.2, p. 34.** "Let α and β be non-zero elements of the group algebra of any torsion-free
  group over the field with two elements. If |supp(α)| = 3 and αβ = 0 then |supp(β)| ≥ 20."

The claim and the route quote these results correctly.
- The hypotheses match: F_2, |supp α| = 3, G torsion-free, and a β of least support for the given α in
  F_2[G].
- The graph class matches: connected, simple, cubic, triangle-free, which is exactly
  `nauty-geng -c -t -d3 -D3`.
- The count 97546 matches the Total row.

**NIT.** Theorem 2.9 is proved by reference to Schweitzer, Theorem 4.2 (arXiv:1202.6645). This review
did not re-read Schweitzer. The claim cites A–T 2.9, and A–T delegates the proof, so the chain of trust
runs one level further than the claim says.

## 2. Quantifiers and scope: PASS

- **Evenness, route step (1).** Over F_2 the coefficient of s in αβ is the number of expressions s = ab
  mod 2. Each (a, s) determines at most one b, so s has one, two or three expressions, and a zero
  coefficient forces exactly two. So 3|B| = 2|S|. The argument never uses minimality, so every support of
  such a β is even, the least one included. This agrees with A–T §6 ("an even positive integer").
- **How 21 is excluded.** Suppose |supp β| ≤ 21. Then the least support n satisfies 20 ≤ n ≤ 21 (A–T
  Cor 6.2), and n is even, so n = 20. The search rules out n = 20, so no β with |supp β| ≤ 21 exists.
  Every odd size is excluded by evenness in the same way.
- **Which groups.** The reduction never leaves G.
  - It left-translates α, which preserves αβ = 0 and every support size.
  - It passes to a least β' in the same F_2[G], which is exactly A–T's standing hypothesis.
  - It reads off the labelled Kaplansky graph.
  So the statement holds for every torsion-free group and every α with |supp α| = 3 over F_2, as the
  claim says. No restriction to a subclass is hidden.
- **Normalization, route step (5).** Left-multiplying α by c^-1 for c ∈ supp α renames the ports by
  a ↦ c^-1 a at every vertex at once. Together with swapping the names x and y, this realizes all of S_3.
  So fixing the root's ports loses nothing. The code works in the opposite group
  (`g_u p = g_v q`), which is again torsion-free, and the relators follow that convention consistently.

## 3. Soundness of `zds3.c`: PASS on the code reading; harness tests PENDING

The landed source (md5 `18a83240ff82d0bcdcdcd33c15780d72`) was read in full.

**Invariant.** Fix a torsion-free realization of any completion of the current partial labelling. Every
coset then has an image in G.
- Seed cosets map to g_v·1, g_v·x and g_v·y.
- A new coset maps to img(f)·s[i].
- Every pointer `T[c][l] = d` is a true equation img(c)·l = img(d).
- `scan` applies relators that hold in G, and `coincide` merges only cosets with equal images, then
  propagates along true pointers.
- So every derived coincidence holds in G.

**The sieves.**
- **Sieve 1.** Tags are edge indices, and distinct edges are distinct elements of S, since each element
  has exactly two expressions. A merge of two differently tagged cosets is therefore a contradiction in
  every group. Vertex injectivity is covered too: `gb[u]` and `gb[v]` carry the edges at port 0 of u and
  of v, which differ because the two ends of an edge have different ports.
- **Sieve 3.** `complete()` asks only that every live coset have all four pointers.
  - With the invariant, the image set is finite and closed under right multiplication by x^±1 and y^±1.
  - So g_root·<x, y> is finite. A torsion-free host forces x = 1, which contradicts the distinct edges at
    ports 0 and 1 of the root.
  - This needs neither stability nor an involutive table.
- **Sieves 2 and 6.** Both add only relators that hold in a torsion-free host: u^k = 1 gives u = 1, and
  the power sieve adds u only when the table shows g·u^e = g for some 2 ≤ e ≤ 8. The exponent sums of a
  cycle word are taken before root extraction, which does not change the rank.
- **Sieve 5.** The rank loop tests whether some 2×2 minor of the exponent-sum matrix is nonzero. The
  theorem of §4 of the artifact, whose proof was re-checked here, applies to G_Γ itself: (*) holds in G_Γ,
  and the only facts used outside (*) hold as statements about indices. So rank < 2 gives a map
  G_Γ → Z that is nonconstant on {1, x, y}, and that is impossible for |A| = 3.
- **DFS.** The root takes the identity port order. Every other vertex tries all six port permutations,
  subject to different ports at the two ends of each edge. A labelling is discarded only when `sieve`
  returns 0, and every surviving leaf prints `SURV`. So `surv 0` on a GRAPH line means no labelling of
  that graph survives the sieves, and by the invariant none is realizable.
- **Input.** `parse_g6` reads the upper triangle column by column, most significant bit first, and
  rejects any vertex of degree other than 3.
- **Limits.** Overflow of `MAXC` exits with code 2. The coincidence queue is bounded by 4·MAXC + 1, and
  `MAXR` and `MAXL` are not reached at n = 20. All 128 shards exited with code 0.

**NIT (no soundness impact).** Take the last step of `scan`, where the forward and backward traces meet.
If the backward end b equals the original forward end f, and s[j−1] is the inverse of s[i], then
`T[b][s[i]^1] = f'` overwrites the pointer `T[f][s[i]] = d1` set earlier in the same scan. Both pointers
are true equations (d1 and f' both stand for img(b)·s[i]), so the overwrite can lose a coincidence but
never invent one. It can only weaken pruning.

**Harness tests (job 692041): PENDING.** The harness includes the landed `zds3.c` unchanged and calls
`sieve` on inputs with known ground truth:
- partial structures genuinely realized in torsion-free groups: Z^2 twice, H_3(Z), BS(1,2) twice, the
  Klein bottle group, F_2 twice, and the Promislow group as affine maps. Any prune there, or any relator
  that is not trivial in the realizing group, is a bug;
- sieve 1 alone on genuine structures in groups with torsion;
- must-fire runs with sieves 2, 3 and 6;
- an independent linear-algebra check of the sieve 5 rank on random complete labellings.

## 4. Aggregation integrity: PASS on the landed records; rerun PENDING

- `check20.595808.out`:
  - 97546 input graphs equal the 97546 graphed ones, all distinct;
  - every GRAPH line reads `surv 0`, and 128 TOTAL lines read `fails 0 budget 0 surv 0`;
  - one option set, `climit 1000 leaf 64000 pw 4 8`, and no nonempty stderr.
- `n20.595808.agg.txt`: 128 shards, `rc!=0 0`, 97546 graphs, `surv 0`, `budget 0`; geng total 97546
  with 0 duplicates.
- `n20b.603674.agg.txt`: the same with `-root 19`, 0 duplicate GRAPH lines.
- The landed `zds3.c` has md5 `18a83240…`. That is the `zds20.c` md5 printed in all 128 shard logs,
  alongside one binary md5 `03dd355c946e27c7780c7d5d460c2121`.
- **NIT.** `n20.sbatch` says the binary "is compiled once from zds3.c before submission" but does not
  record the compile command. `ladder.sbatch` and `exp14.sbatch` use `gcc -O2 -std=gnu99 -Wall`.
- **PENDING (job 692041).**
  - `nauty-geng -c -t -d3 -D3 -u 20`;
  - a fresh build of the landed source;
  - a rerun of 47 sampled n = 20 graphs (45 random, plus the two heaviest) with roots 0 and 19, compared
    per graph (nodes, surv) against `r20.lines.txt.gz` and `r20b.lines.txt.gz`.

## 5. Novelty statement and the prior bounds: PASS

- **Nielsen–Soelberg, read in the preprint.** `mathdept.byu.edu/~pace/KaplanskyConjecture_web.pdf`,
  6 pages, run through `pdftotext -layout`.
  - Theorem 1.4 (pp. 2–3): "Let A and B be subsets of a torsion-free group. Assuming AB has no unique
    product, then |A| + |B| ≥ 16. More specifically, … If |A| = 3, then |B| ≥ 19."
  - The remark after it: "(The bound |supp(β)| ≥ 20 in the case R = F2, given in [1], is also a
    consequence of our bound.)" [1] is A–T.
  - The claim's sentence about N–S is accurate: ≥ 19 over any domain, which recovers the F_2 bound 20
    through evenness and does not improve it.
- **Wording.** The claim asserts no priority or novelty. It states the result and places it against A–T
  Cor 6.2 and Thm 6.1 and N–S Thm 1.4. The lane's report says "new relative to every source checked, not
  a proven exhaustive novelty check", which is honest.
- **Spot-check for a later bound of 21 or more (not exhaustive).**
  - The arXiv search "Kaplansky zero divisor support" returns 2501.07646 (CAT(0) groups), 1709.08204
    (support 4), 1612.00934 (A–T) and 1110.3692 (convolution algebras). None of their abstracts states a
    bound above 20 for support 3.
  - Semantic Scholar lists two papers citing A–T. One is Tabei, 2607.18346, which works inside the
    Promislow group only. The other is the journal version of A–T itself, with the same abstract and
    bound 20.
  - The arXiv API refused queries ("Rate exceeded"), so the search is not exhaustive.
  - No bound of 21 or more over F_2 for |supp α| = 3 was found.
