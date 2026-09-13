# Open status of Zaremsky's Section 1 problems, part 1 (2026-09-13)

Source list: M. C. B. Zaremsky, *Some open problems*, version dated July 12, 2026
(https://zaremsky.github.io/open_problems.pdf, SHA-256
`d14c2ce7c26b60363693d1c549f5a25d51ab271e15e5ff4fa8215477d30cde50`), Section 1
"Finiteness properties, BNSR-invariants, and Dehn functions". Hub claim:
`zaremsky-open-problems-2026-07-12`. Scope of this sweep: the problems the list itself
leaves open, 1.01, 1.03–1.14 and 1.16–1.25. Problems 1.02 and 1.15 are answered in the
list's own notes and are handled by the hub lane.

Part 1 has the method, the summary table and details for 1.01–1.10. Part 2
(`zp-open-status-section-1-2026-09-13-part2.md`) has details for 1.11–1.25.

## How bounded the search was

- Date of search: 2026-09-13. Tools: a general web search index and arXiv abstract and
  HTML pages. There was no MathSciNet and no zbMATH access.
- The arXiv export API returned HTTP 429 (rate limit) on two of three queries. The
  session's web-search budget (200 calls, shared across lanes) ran out partway
  through, so later problems got fewer searches. The per-problem effort is in the table.
- Verification levels used below:
  - **HTML**: statements read from the arXiv HTML text.
  - **abstract**: from the arXiv abstract page only; theorem numbers not checked.
  - **snippet**: only from a search-result summary. Treat as a lead, not a citation.
- "No answer found" means none turned up in this bounded search. It is not a claim that
  no answer exists. An owner lane that relies on a status should re-read the source.

## Summary table

| Problem | Status (2026-09-13) | Strongest sources found | Effort |
|---|---|---|---|
| 1.01 | open | Fournier-Facio–Zaremsky arXiv:2607.21727 (Higman's rope trick never gives FP_3(Q); cites [Zar] 1.1 as open) | 4 searches + HTML |
| 1.03 | open, no answer found | Alonso 1994 (F_n is a quasi-isometry invariant), per snippet | 2 searches |
| 1.04 | open, no answer found | background only: Leary arXiv:1512.06609, Brown–Leary arXiv:2004.04550 | 2 searches |
| 1.05 | open | Huang arXiv:2602.17982 (K(π,1) reduced to tree diagrams); Paolini–Salvetti arXiv:1907.11795 (affine) | 1 search + abstract |
| 1.06 | open (known for many families) | Escartín Ferrer arXiv:2501.08692 (Σ¹-conjecture for balanced Artin groups) | 2 searches + abstract |
| 1.07 | open (known for many classes) | von Puttkamer–Wu arXiv:1807.10095 (Artin groups), arXiv:1704.05304 (linear groups) | 2 searches + abstracts |
| 1.08 | open, no answer found | background only (Farley–Sabalka discrete Morse theory; RAAG case via Meier–VanWyk) | 3 searches |
| 1.09 | open (partial results known) | Koban–McCammond–Meier arXiv:1306.4046 (Σ¹); Zaremsky arXiv:1507.08597 (separations) | 3 searches + abstract |
| 1.10 | open | Juschenko–Monod arXiv:1204.2132 (only finitely generated examples) | 2 searches |
| 1.11 | open | Button–Thillaisundaram arXiv:1007.2845 (p-deficiency no-go) | 1 search + abstract |
| 1.12 | open | Fisher arXiv:2112.00397 §1 (the finite-cd version is also open) | 3 searches + HTML |
| 1.13 | open, no answer found | dense-or-empty results: Ershov–Zaremsky arXiv:2505.18826; arXiv:2606.26033 | 1 search + abstracts |
| 1.14 | open, no answer found | Zaremsky arXiv:2405.09722 (many RN groups have finite abelianization) | 2 searches |
| 1.16 | open, partial result known | Zaremsky arXiv:2305.15176 (at least exponential Dehn function) | 1 search + abstract |
| 1.17 | **partly answered after the list's date** | Llosa Isenrich–Weis arXiv:2608.07191 (2026-08-07) | 1 search + abstract |
| 1.18 | open, no example found | background only: P_n separations (arXiv:1507.08597) | 1 search |
| 1.19 | open, no answer found | Roy arXiv:2607.08900 (presentations of RAAG kernels), related only | 1 search + abstract |
| 1.20 | open, no answer found | Llosa Isenrich–Schesler–Wu arXiv:2510.01952 (countably many simple groups with prescribed finiteness properties) | 3 searches + HTML |
| 1.21 | open; reduction recorded in part 2 | Ferry–Ranicki arXiv:math/0008070 §2 (no torsion-free π with K̃_0(Zπ) ≠ 0 known) | 1 search + HTML |
| 1.22 | open | Hyde–Lodha arXiv:2302.04805 (type F∞, infinite geometric dimension) | 2 searches + abstract |
| 1.23 | open | Chang–García-Mejía–Migliorini arXiv:2507.07566 (Dehn functions of BB groups classified) | 1 search + abstract |
| 1.24 | open, no answer found | Lee arXiv:1212.0257 (exponential upper bound) | 3 searches + abstract |
| 1.25 | open (posed 2025) | the question is Llosa Isenrich–Schesler–Wu arXiv:2510.01952 Question 1.12 | 2 searches + HTML |

No Section 1 problem in scope was found fully answered. Messages sent to owner lanes:
z1-17-dehn-cocompact (2608.07191), z1-01-embed-pos and z1-01-embed-neg (2607.21727),
z1-23-bb-dehn (2507.07566, 2607.08900), z1-06-bns-artin (2501.08692 and related),
z1-21-type-f-proof and z1-21-wall-obstruction (the reduction in part 2).

## Details, 1.01–1.10

### 1.01 — every group of type F_n embeds in a group of type F_{n+1}? of type F_∞?
- **Status:** open.
- **Fournier-Facio–Zaremsky**, "Finiteness properties and Higman's rope trick",
  arXiv:2607.21727, submitted 2026-07-23 (HTML).
  - The introduction calls the higher-dimensional Higman/Leary embedding question "a
    fundamental open question (see [Bes], Q 8.7, [KM], 21.146, [Zar], 1.1)".
  - Theorem A: if every finitely generated recursively presented group embeds into a
    recursively presented group of type FP_n, then every finitely presented group embeds
    into a group of type F_n.
  - Theorem B: for an infinite G = F/R with R ≠ 1, H_3(Hig_ι(G), Q) is infinite
    dimensional, so the rope-trick group is not of type FP_3(Q).
  - Questions 1.3 and 1.4 there: does every finitely generated recursively presented group
    embed in a group of type F_3 (F_∞)? Does every finitely generated group embed in a
    group of type FP_3 (FP_∞)?
- **Leary**, arXiv:1610.05813, *Subgroups of almost finitely presented groups* (Math.
  Ann.): every countable group embeds in a group of type FP_2 (snippet; also quoted in
  Zaremsky 1.25 and in the FFZ abstract).
- **Consequence for the lanes:** the rope trick is a dead method above FP_2. The obstruction is
  to a method, not to the embedding.

### 1.03 — quasi-isometric to an (n−1)-connected proper metric space ⇒ type F_n?
- **Status:** open; no answer found.
- **Background (snippet):** Alonso, "Finiteness conditions on groups and
  quasi-isometries", J. Pure Appl. Algebra (1994): F_n and FP_n are quasi-isometry
  invariants among groups. Kapovich–Kleiner and Druţu–Kapovich characterize F_n by
  coarse (n−1)-connectedness.
- **Gap between the notions:** the problem asks about topological (n−1)-connectedness of
  some proper space quasi-isometric to G, which need not be coarsely (n−1)-connected
  uniformly. That gap is the whole question.

### 1.04 — FP_n ⟺ FH_n?
- **Status:** open; no answer found.
- **Background:**
  - FH_n = a free (or, in Zaremsky's phrasing, proper) cocompact action on an
    (n−1)-acyclic complex.
  - Bestvina–Brady groups over an acyclic, non-simply-connected flag complex are of type
    FH but not F_2 (snippet).
  - Leary, arXiv:1512.06609 (uncountably many groups of type FP); Brown–Leary,
    arXiv:2004.04550 (groups of type FP via graphical small cancellation);
    Leary–Saadetoğlu, *Some groups of finite homological type* (snippet).
- None of these separates FP_n from FH_n.

### 1.05 — are all Artin groups of type F_∞?
- **Status:** open.
- **Reduction:** the K(π,1) conjecture for an Artin group gives a finite classifying space
  (the Salvetti complex), hence type F.
- **Known K(π,1) cases:**
  - spherical (Deligne); expository proof in arXiv:2607.24659 (July 2026, abstract);
  - affine: Paolini–Salvetti, arXiv:1907.11795 (Invent. Math. 2021);
  - summary of the affine proof: arXiv:2509.00445 (snippet);
  - FC type and 2-dimensional: classical.
- **Huang**, arXiv:2602.17982 (2026-02-20, abstract): reduces the K(π,1) conjecture for
  all Artin groups to properties of Artin groups whose Coxeter diagrams are trees, and
  deduces new K(π,1) classes. The abstract states no F_∞ consequence.

### 1.06 — compute Σ¹(A) for every Artin group A
- **Status:** open in general; known for many families.
- **Escartín Ferrer**, "On the Σ¹ and Σ²-invariants of Artin groups", arXiv:2501.08692
  (v1 2025-01-15, revised 2025-07-14, abstract):
  - proves the "Σ¹-conjecture" for Artin groups in which some prime p divides l(e)/2
    for every even label l(e) > 2;
  - proves it for balanced Artin groups, which extend Kochloukova's family
    (arXiv:2009.14269) and the coherent Artin groups;
  - states a Σ²-conjecture under K(π,1), proved for 2-dimensional and coherent Artin
    groups, and computes Σⁿ for all n ≥ 2 in the 2-dimensional case.
- **Earlier work:**
  - de Almeida, arXiv:1605.00271 (J. Group Theory 2016): Σ¹ for a class of Artin groups
    with minimal graphs of arbitrary circuit rank;
  - circuit rank 2 (J. Group Theory 2017, snippet);
  - arXiv:2309.03091 (Artin groups satisfying K(π,1));
  - arXiv:2011.07608 (even Artin groups of FC type).
- **Natural answer claim:** the Σ¹-conjecture for all Artin groups. Its exact statement is in
  the introduction of 2501.08692; not read here.

### 1.07 — Juan-Pineda–Leary and von Puttkamer–Wu conjectures
- **Status:** open in general.
- **von Puttkamer–Wu**, arXiv:1807.10095 (Algebr. Geom. Topol. 20 (2020) 2885–2904,
  abstract):
  - an Artin group has a finite model for E_VCyc(G) iff it is virtually cyclic, which
    settles the JPL conjecture for Artin groups;
  - conjugacy growth of CAT(0) groups containing Z² is faster than linear, which gives an
    alternative proof for CAT(0) cube groups;
  - for poly-Z groups, B_VCyc(G) is homotopy finite iff G is cyclic.
- **von Puttkamer–Wu**, arXiv:1704.05304 (IMRN, abstract): the JPL conjecture for linear
  groups.
- A snippet also credits them with one-relator, acylindrically hyperbolic and 3-manifold
  groups. That attribution was not checked.
- **Barnea–Camina–Ershov–Lewis**, arXiv:2210.15746 (Math. Ann. 392 (2025) 1747–1779,
  abstract): determines all residually finite discrete groups with finite NCC, the number
  of cyclic subgroups whose conjugates cover G. That is the cyclic-covering analogue; its
  bearing on the von Puttkamer–Wu conjecture was not checked.

### 1.08 — BNSR invariants of graph braid groups
- **Status:** open; no computation found (3 searches; the arXiv title query hit the rate
  limit).
- **Leverage:**
  - Farley–Sabalka discrete Morse theory (presentations);
  - graph-of-groups decompositions of graph braid groups (arXiv:2209.03860);
  - when a graph braid group is a right-angled Artin group, Σ¹ follows from Meier–VanWyk
    (arXiv:math/9310202) and the higher invariants from Meier–Meinert–VanWyk;
  - Σ¹ of braid and pure braid groups of the sphere, projective plane, torus and Klein
    bottle: arXiv:2308.12377.
- The characterization of which graph braid groups are RAAGs (Kim–Ko–Park) was not
  re-located, because the web budget ran out.

### 1.09 — BNSR invariants of pure braid groups
- **Status:** open for the higher invariants; partial results known.
- **Σ¹(P_n):** Koban–McCammond–Meier, *The BNS-invariant for the pure braid groups*,
  arXiv:1306.4046 (Groups Geom. Dyn.): the complement of the union of the P_3-circles and
  P_4-circles (snippet).
- **Zaremsky**, arXiv:1507.08597 (Publ. Mat. 61 (2017), abstract):
  - Σ^{m−2}(P_n) ⊊ Σ^{m−3}(P_n) for 3 ≤ m ≤ n;
  - Σ^∞(P_n) = Σ^{n−2}(P_n);
  - explicit characters separating consecutive invariants.
- **Still open:** the exact Σ^m(P_n) for 2 ≤ m ≤ n−2.

### 1.10 — a finitely presented (or F_∞), infinite, simple, amenable group
- **Status:** open.
- **Juschenko–Monod**, arXiv:1204.2132 (Ann. of Math. 2013): finitely generated infinite
  simple amenable groups, the commutator subgroups of topological full groups of minimal
  Cantor systems (Matui). A snippet from Juschenko's lecture notes says these are never
  finitely presented.
- The fp simple left-orderable groups of Hyde–Lodha (arXiv:2302.04805) are not known to be
  amenable.
- No 2025–2026 answer found.
