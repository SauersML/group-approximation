# Swarm note: `fpbs-pivotal-budget-universal`, 2026-09-16

Agent `swarm-fpbs-pivotal-budget-universal`. It locked the hole
`fpbs-pivotal-budget-universal` and worked on the target itself.

## 0. Setup

The target (PB) asks that every nonamenable Cayley graph `G = Cay(Gamma,S)`,
with `c = p_c(G)`, admit a constant `C` and a `p0 > c` such that

    E_p[N_(n,R) | E_(n,R)] <= C n     for all n >= 1, R >= n, p in [c, p0].

Here:

* `E_(n,R)` is the event that `e` connects to `X_n` inside `B_R`;
* `N_(n,R)` is the number of open pivotal edges for that connection;
* `X` is the simple or lazy random walk.

The setup is Section 1 of
`research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`.

By that note's Section 3, PB implies IS, which implies NC, which implies
`fpbs-benjamini-schramm-universal`; also PB implies RATE, which implies the
same. So the universal target is at least as hard as the Benjamini–Schramm
conjecture `p_c<p_u` on every nonamenable Cayley graph. I did not expect to
settle it. The aim was a sound, recorded extension of the class on which PB is
proved.

Before this session the archive had PB with a bounded count on the class `C_2`
of nonamenable Cayley graphs with `p_c<p_(2->2)`. That is Corollary 4.2 of the
kernel note, recorded as `fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels`.
The gap itself was recorded in three cases:

* Gromov hyperbolic graphs;
* graphs with a quasi-transitive nonunimodular automorphism subgroup;
* free products on union generating sets.

## 1. What was established

Artifact: `research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md`.

* **Theorem A** (`fpbs-acylindrically-hyperbolic-critical-l2-gap`, route
  `fpbs-acylindrically-hyperbolic-critical-l2-gap-citation`). For every
  acylindrically hyperbolic group `G` and every finite generating set `S`,
  `p_c(Cay(G,S)) < p_(2->2)(Cay(G,S))`.
* **Corollary B** (`fpbs-acylindrically-hyperbolic-pivotal-kernels`, route
  `fpbs-acylindrically-hyperbolic-pivotal-kernels-proof`). All four pivotal
  kernels hold on these graphs, and PB holds with `C = C_0 = 2d||T_(p0)||^2`
  and a count bounded independently of `n`.

How it was proved:

1. Choi–Seo (arXiv:2508.08932v2) prove the two estimates
   - (Gamma1): `limsup (p_c-p) chi_p < infinity`, and
   - (Gamma2): `1 - iota(T_p) -> 0` as `p -> p_c-`

   on every such Cayley graph. See `thm:hutchcroft1plus2` with line 1537, and
   `cor:hutchcroftIotaAcyl`.
2. Hutchcroft's `prop:criterion` (arXiv:1804.10191, label line 514) says that
   `p_c<p_(2->2)` if and only if
   `liminf ((p_c-p)/(1-p)) chi-bar_p sqrt(1-iota(T_p)^2) < 1/||A||`.
3. Since `1-iota^2 <= 2(1-iota)` and `p_c<p_u<=1`, the two estimates make the
   liminf equal to `0`. So the criterion gives the gap.
4. Corollary B follows from Theorem A, Osin's free-subgroup corollary
   (`fpbs-osin-ah-groups-not-products-not-torsion`, for nonamenability) and
   Corollary 4.2 of the kernel note.

Honest framing:

* Choi–Seo state only `p_c<p_u` and `nabla_(p_c)<infinity` as theorems. But
  their introduction (line 242) says the triangle condition "is derived from
  yet another fact, namely, the `L^2`-boudedness". Theorem A is therefore
  implicit in their paper.
* The contribution here is the explicit, checked deduction and its entry into
  the archive, which makes Corollary B available.
* No new case of `p_c<p_u` arises. The target stays OPEN.

Newly covered examples include:

* surface mapping class groups containing `Z^2`, on any generating set;
* free products with a non-hyperbolic factor, such as `Z^2 * Z`, on
  generating sets that are not unions of generating sets of the factors.
  (Referee correction: if both factors are hyperbolic, the product is
  hyperbolic and was already covered.)

## 2. Approaches and where they die

### 2.1 Enlarging the l2-gap class (succeeded; Section 1)

Hutchcroft's criterion is an equivalence. On a Cayley graph, (Gamma1) together
with (Gamma2) is exactly `p_c<p_(2->2)`: the "only if" proof at [H] line 543
uses `lem:Cheeger`'s lower bound `chi-bar_p(1-iota) <= ||T_p||`. So any paper
that proves the two Hutchcroft estimates proves the gap. Choi–Seo is the only
one found that does so beyond hyperbolic graphs.

The deduction gives no explicit lower bound on `p_(2->2)-p_c`. [CS] give no
rate in (Gamma2) and no explicit constant in (Gamma1).

### 2.2 Other classes (die at missing inputs)

* **Products, e.g. `F_2 x Z` on an arbitrary generating set.** These are not
  acylindrically hyperbolic (`fpbs-osin-ah-groups-not-products-not-torsion`).
  [CS] line 286 says "Our method does not handle such groups, including
  `F_2 x Z`". They pose `ques:f2z`, which asks even for `p_c<p_u`, and report
  in their acknowledgement that Hutchcroft confirmed the question is still
  open. The scan in Section 3 found no 2024–2026 paper answering it.
* **Hyperbolic modulo an infinite normal subgroup.**
  `fpbs-hyperbolic-quotient-fibre-estimates-l2-gap` gives the gap only
  conditionally, on two fibre estimates that remain open there.
* **Infinite amenable wq-normal subgroups.** This is the other branch of
  `fpbs-amenable-splittings-are-ah-or-amenable-wq-normal`. No gap input is
  known for it.

### 2.3 Converse: does PB force `p_c<p_(2->2)`? (no argument found)

If it did, the universal target would be equivalent on Cayley graphs to
`fpbs-nonamenability-bounds-critical-connectivity-operator`. The natural
argument uses PB through Russo's formula for
`a_(n,R)(p) = P_p(e <-> X_n in B_R)`.

* PB gives `a_(n,R)(p0) <= (p0/c)^(C n) a_(n,R)(c)`. After `R -> infinity`,
  the growth rate satisfies `lambda(p0) <= rho (p0/c)^C`.
* Everything obtained this way is a statement about the moments
  `a_n(p) = tau(P^n T_p)`. Here:
  - `P` is the random-walk operator;
  - `T_p` is the connectivity operator;
  - `tau(x) = <x delta_e, delta_e>` is the trace on the right group von
    Neumann algebra `R(G)`.
* Those moments depend on `T_p` only through its conditional expectation onto
  the abelian algebra `W*(P)`. A positive operator whose conditional
  expectation onto an abelian subalgebra is bounded need not be bounded. For
  example, an element free from that subalgebra has constant conditional
  expectation.

So the argument cannot reach `||T_p|| < infinity` without percolation structure
beyond the moments. I found none. This is recorded only here, because it is a
heuristic obstruction to one proof strategy, not a theorem.

### 2.4 A trace proof of the upper bound (duplicate, note only)

If `T_p` is bounded then `a_n(p) <= rho^n` for all `n`. Proof:

* `T_p >= 0`, since `<T_p f,f> = E sum_C |sum_(g in C) f(g)|^2`.
* `T_p` and `P` both commute with left translations, so they lie in `R(G)`.
* `P^n <= rho^n` because `P` is self-adjoint.
* So `a_n = tau(T_p^(1/2) P^n T_p^(1/2)) <= rho^n tau(T_p) = rho^n`.

This is Hutchcroft's `prop:nonuniquenessatpell2` ([H] label line 1721) for
`p<p_(2->2)`. The kernel note already uses that proposition (Lemma 2.3), so no
node was created.

### 2.5 The universal target via Theorem 4.1 (dies as in the kernel note)

The only general bound in the archive is
`E_p[N|E] <= p W_n(p)/mu^n(e)`, from Theorem 4.1(a) of the kernel note.

* Proposition 6.1 there shows that `W_n(p) = infinity` at every uniqueness
  parameter. So the bound certifies nonuniqueness and cannot derive it.
* Section 6.3 there shows that the ball-truncated `W_(n,R)` increases to
  `W_n`. So any universal proof must control the pivotal event inside `B_R`
  uniformly in `R>=n`.

This session added nothing there. The obstruction stands.

## 3. Literature gate

All fetches were done on 2026-09-16 through the arXiv API and e-print
endpoints. Line numbers refer to the TeX sources named below.

### 3.1 Primary sources, read in the TeX at the cited lines

* **[H]** T. Hutchcroft, *Percolation on hyperbolic graphs*, arXiv:1804.10191.
  - Read from the TeX e-print `HyperbolicPercolation6.tex` (gzip timestamp
    2019-03-27).
  - Labels used: `prop:2to2givesqtoq` (line 397), `cor:l2AizBar` (449),
    `prop:criterion` (514), `lem:Cheeger` (529), the criterion's proof (543)
    and `prop:nonuniquenessatpell2` (1721).
  - The journal venue is from memory and unverified, so it is not cited.
* **[CS]** I. Choi and D. Seo, *Percolation in acylindrically hyperbolic
  groups*, arXiv:2508.08932v2.
  - v1 dated 2025-08-12, v2 dated 2025-08-13. Comment: "61 pages, 3 figures";
    no journal reference in the API metadata.
  - Read from the TeX e-print `perc.tex`.
  - Labels used:
    - the introduction at lines 242–245;
    - the products remark at line 286 and `ques:f2z` (288);
    - (Gamma1) and (Gamma2) as displayed at lines 540–542;
    - `thm:hutchcroft1plus2` (561), proved in Appendix A (line 2222 onward);
    - line 1537, where the hypothesis of that theorem is verified for
      acylindrically hyperbolic groups;
    - `cor:hutchcroftIotaAcyl` (2195).
  - The paper is unrefereed as far as the metadata shows. I checked the
    statements used and how they fit together, but did not re-check the
    proofs in Sections 4–7 or Appendix A.

### 3.2 Sources used through archive nodes

* D. Osin, arXiv:1304.1246 (acylindrically hyperbolic groups), through
  `fpbs-osin-ah-groups-not-products-not-torsion`. Not re-fetched in this
  session.
* The kernel note
  `research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`,
  Sections 1, 3, 4 and 6.

### 3.3 Scan for 2024–2026 work

The arXiv API query was
`search_query=abs:percolation AND (abs:nonamenable OR abs:non-amenable)`,
with 25 results, newest first. Of the 2024–2026 entries:

* **Abstracts read.**
  - 2608.06644v2 (2026-08-06), *Applications of the cluster graphing*;
  - 2511.23317v1 (2025-11-28), *Vanishing uniqueness thresholds in Voronoi
    percolation on products*;
  - 2502.02560v2 (2025-02-04), *Weighted-amenability and percolation*;
  - 2409.12283v1 (2024-09-18), *Percolation at the uniqueness threshold via
    subgroup relativization*.
* **Titles only.**
  - 2512.07740v1 (2025-12-08), on factor of IID percolations;
  - 2512.06640v3 (2025-12-07), on the frog model;
  - 2504.02435v1 (2025-04-03), Poisson–Voronoi percolation in higher rank;
  - 2412.17768v2 (2024-12-23), GFF level sets;
  - 2412.15895v1 (2024-12-20), dimension jump in `infinity+d` dimensions;
  - 2407.15079v1 (2024-07-21), random walk on dynamical percolation.
* **Older entry seen but not re-read.** Hutchcroft, *The L^2 boundedness
  condition in nonamenable percolation*, arXiv:1904.05804v2 (v1
  2019-04-11).

None of these, as far as the abstracts and titles show:

* proves the universal pivotal budget or `p_c<p_u` on every nonamenable
  Cayley graph;
* answers `ques:f2z`;
* states `p_c<p_(2->2)` explicitly for acylindrically hyperbolic groups.

The scan covers one query. A referee should treat "not in the literature" as
unverified beyond it.

## 4. Files

Created in this session; no existing file was modified:

* `research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md`: artifact with
  Theorem A, Corollary B, quotes and weakest steps.
* `research/fpbs-acylindrically-hyperbolic-critical-l2-gap.md`: claim.
* `research/fpbs-acylindrically-hyperbolic-critical-l2-gap-citation.md`: route
  with `requires: []` (imports plus deduction).
* `research/fpbs-acylindrically-hyperbolic-pivotal-kernels.md`: claim.
* `research/fpbs-acylindrically-hyperbolic-pivotal-kernels-proof.md`: route.
* `notes/fpbs-pivotal-budget-universal-swarm-2026-09-16.md`: this note.

No experiments were run, so there is no `experiments/` directory.

## Referee (2026-09-16)

**What was checked.**

* All six solver files were read in full. The referenced nodes were read too:
  `fpbs-sc-choi-seo`, `fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels` and
  its proof, `fpbs-osin-ah-groups-not-products-not-torsion`,
  `fpbs-hyperbolic-nonunimodular-critical-l2-gap-citation`, and the context of
  `fpbs-pivotal-budget-universal`. `git status` showed no unlisted solver
  files.
* **Primary sources, re-fetched independently.** The referee downloaded both
  TeX e-prints. The arXiv 2508.08932v2 gzip is dated 2025-08-14; the
  1804.10191 gzip, `HyperbolicPercolation6.tex`, is dated 2019-03-27. Every
  quoted label and line number was confirmed verbatim:
  - [H]: line 288 (`p_(q->q)`), 301 (`p_(q->q) <= p_u`), 397, 449
    (`cor:l2AizBar`), 507 (`iota(T_p)`), 514–520 (`prop:criterion`), 529
    (`lem:Cheeger`, both inequalities, for `0<p<p_(1->1)`), 542–543 (the
    proof), 1721.
  - [CS]: line 204 (the Cayley graph convention), 216, 236, 242, 286–288, 485–499,
    505, 540–542 ((Gamma1), (Gamma2)), 561 (`thm:hutchcroft1plus2`), 925 (the
    definition), 1224, 1537, 2195–2217 (`cor:hutchcroftIotaAcyl` and its
    proof), 2222 (Appendix A).
* **arXiv abstract page of 2508.08932**, fetched 2026-09-16. The latest
  version is still v2 (2025-08-13), with no journal reference, and the
  abstract does not mention `p_(2->2)`.
* **arXiv abstract of 1304.1246**, fetched 2026-09-16. It confirms that the
  AH class coincides with the groups that have a non-elementary WPD action on a
  hyperbolic space. This matches the [CS] definition at line 925. The number
  "Theorem 1.2" is still unverified.
* **The deduction was recomputed.** `K={e}` gives `s>=1/chi_p`, and row sums
  give `s<=1`. Then `1-iota^2 = s(2-s) <= 2s`, and
  `(p_c-p)chi_p <= M+1` near `p_c`. Also `1-p >= 1-p_c > 0`. So the liminf is
  `0`. The "if" direction of `prop:criterion` was re-derived from
  `lem:Cheeger` and `cor:l2AizBar`, and it is correct. Remark A.1, that on
  Cayley graphs (Gamma1) with (Gamma2) is equivalent to the gap, matches the
  "only if" proof at [H] line 543. There `iota(T_p) -> 1`, which is exactly
  (Gamma2).
* **Circularity.** None. [CS] obtain (Gamma1) and (Gamma2) geometrically, and
  they use Hutchcroft's criterion only in its weakened form.
* **Corollary B.** The hypotheses of Corollary 4.2 (a nonamenable Cayley graph
  with `p_c<p_(2->2)`) are supplied exactly: by Osin item 2 and by Theorem A.
  The quantifiers (`n>=1`, `R>=n`, `p<=p0`) match the established node.
* **Duplicates.** `bin/cairn search --similar` on both claims found no
  duplicate. The nearest nodes (`fpbs-sc-choi-seo`,
  `fpbs-hyperbolic-nonunimodular-critical-l2-gap`,
  `fpbs-free-product-cayley-graphs-have-critical-l2-gap`,
  `fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels`) are all separated in
  `distinct_from`. The OPEN nodes `fpbs-hyperbolic-quotient-every-generating-set`
  and `fpbs-seifert-fibred-every-generating-set` are not settled. The Seifert
  groups and `F_2 x Z` have infinite centre, and products of two infinite groups
  are excluded by Osin, so none of them is AH. The hyperbolic-quotient class
  does contain some AH groups, for example a free group mod an infinite normal
  subgroup with hyperbolic quotient, but not all of its members are AH.
* **Discipline.** The ids are 46–55 characters. There are no new holes. The
  `requires: []` route is a literature import followed by a complete
  elementary deduction, which the README allows ("Literature imports are
  direct-proof routes"). The trust surface is the same unrefereed preprint
  already imported by `fpbs-sc-choi-seo-proof`, and both the node and the
  artifact say so.

**What was changed.**

* The artifact (Section 5.2) and this note (Section 1) listed "free products
  on non-union generating sets" as newly covered. The referee added that this
  is new only when some factor is non-hyperbolic (e.g. `Z^2 * Z`), because a
  free product of hyperbolic groups is hyperbolic and was already covered.
* In artifact Section 6, item 3, the referee recorded the fetched Osin
  abstract.

**Verdict.** Sound and honestly labelled. Theorem A is an import from an
unrefereed preprint plus a correct short deduction, and it is correctly
described as implicit in [CS], not as new mathematics. Corollary B is a valid
composition of established nodes. The universal target
`fpbs-pivotal-budget-universal` remains OPEN. Landed with the small fixes
above.
