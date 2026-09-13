# Unique Games Conjecture: verified state of the art, September 2026

Lane `ex-ugc`, 2026-09-12. Each item gives its **verification level**:

* **[PDF]** the theorem statement was read from the source PDF, at the stated
  number;
* **[abs]** only the arXiv abstract page was read;
* **[recalled]** stated from background knowledge and not re-read. These must
  not be used in a proof step.

Cairn ids are given where a node exists. **Status of UGC: OPEN.**

## 1. Hardness side

1. **2-to-2 Games Theorem** [PDF]. Khot--Minzer--Safra, ECCC TR18-006
   (FOCS 2018), Theorem 1.4: for every `eps > 0` there is `l` with
   `Gap 2-to-2[F_2^l](1-eps, eps)` NP-hard. It completes KMS17, DKKMS18 (two
   papers) and BKS19. Completeness is imperfect; the perfect-completeness 2-to-2
   and 2-to-1 conjectures remain open. Node `two-to-two-games-theorem`.
2. **Unique games at completeness one half** [derived here]. Splitting each
   2-to-2 constraint gives NP-hardness of `Gap-UG((1-eps)/2, eps)`. Node
   `unique-games-hard-at-completeness-one-half`.
3. **SSEH implies UGC** [PDF]. Raghavendra--Steurer, STOC 2010, Conjecture 1.3
   and Theorem 1.4. Raghavendra--Steurer--Tulsiani, arXiv:1011.2586, Corollary
   3.3: SSEH is equivalent to UGC on instances with near-perfect small-set
   expansion. No implication UGC => SSEH is known (BBKSS, page 2, [PDF]).
   Nodes `small-set-expansion-hypothesis`,
   `small-set-expansion-hypothesis-implies-ugc`,
   `ugc-from-small-set-expansion-hypothesis`.
4. **Rich 2-to-1 Games** [repository citation]. Braverman--Khot--Minzer, ITCS
   2021: the Rich 2-to-1 Conjecture is equivalent to UGC. This is the
   repository's main proof-side region: `rich-2to1-games-conjecture`,
   `smooth-design-rich-2to1-hardness` (open crux), and many landed obstructions.
5. **Multilayered 2-to-2 PCPs, 2026** [repository source record, HTML
   rendering]. Karthik C. S.--Minzer, arXiv:2609.06775v1 (6 September 2026),
   Theorems 1.4 and 1.6. They give tight `k - eps` hardness of `k`-uniform
   hypergraph vertex cover for `k >= 4` without UGC, via multilayered label cover
   with 2-to-2 constraints and completeness `1 - eps`. It is unrefereed, and the
   authors credit ChatGPT 5.6 Pro. Node
   `k-uniform-hypergraph-vertex-cover-hardness-without-ugc`.
6. **Definability, 2025** [abs]. Dawar--Molnar, arXiv:2504.03523 (CSL 2025;
   v2 1 March 2026). Constant-factor approximation of weighted 2-to-2 games is
   not definable in fixed-point logic with counting, *with perfect completeness*.
   This is a logic-side result; NP-hardness with perfect completeness remains
   conjectured.
7. **Quantum label cover, 2025** [abs]. Culf--Mastel--Paddock--Spirig,
   arXiv:2510.03477 (3 October 2025): quantum smooth label cover is RE-hard and
   undecidable, in contrast with quantum unique label cover, which is efficiently
   solvable (Kempe--Regev--Toner [recalled]). This touches the repository's
   operator region `perfect-commuting-unique-game-is-classically-satisfiable`.

## 2. Algorithmic side

1. **Basic SDP.** Charikar--Makarychev--Makarychev (STOC 2006) round
   `1 - eps` to `1 - O(sqrt(eps log k))` [recalled]. On symmetric quotient
   instances over `F_p^N` the loss is linear, `Theta(eps log k)` [derived here,
   `elementary-abelian-galois-games-round-with-linear-loss`].
2. **Subexponential time.** Arora--Barak--Steurer (FOCS 2010; JACM 2015) run in
   time `exp(n^(poly(eps)))`-type via threshold rank [recalled; source not
   retrieved]. Barak--Gopalan--Hastad--Meka--Raghavendra--Steurer,
   arXiv:1111.0405 [abs]: there are small-set expanders with more than
   `exp(log^delta n)` eigenvalues above `1 - eps`, answering ABS's question.
3. **2 -> q norms and SoS** [abs]. Barak--Brandao--Harrow--Kelner--Steurer--Zhou,
   arXiv:1205.4484v3. SSE holds iff the top-eigenspace projector has bounded
   `2 -> q` norm. Constant rounds of SoS refute the noisy-cube and short-code UG
   integrality-gap instances.
4. **Certified small-set expanders** [PDF]. Bafna--Barak--Kothari--Schramm--Steurer,
   arXiv:2006.09969v3: Theorem 1.1, Corollaries 1.3--1.4, Theorem 1.5. Affine UG
   is solvable in polynomial time on certifiably hypercontractive graphs, the
   noisy hypercube, the short code and Johnson graphs. It is open whether
   constant-degree SoS solves UG on the non-noisy Boolean cube. Node
   `affine-ug-easy-on-certifiably-hypercontractive-graphs`.
5. **Globally hypercontractive graphs** [PDF]. Bafna--Minzer, arXiv:2304.07284
   (CCC 2024), Theorems 1.5--1.8: affine UG on noisy Johnson, Grassmann and HDX
   walks at any constant completeness. Node
   `affine-ug-easy-on-globally-hypercontractive-graphs`.
6. **Refutation form.** Node `unique-games-gap-admits-polynomial-time-algorithm`
   (open) collects these, with where each stops.

## 3. What changed in this repository on 2026-09-12 (lane ex-ugc)

* **Galois games.** These are unique games whose lift is a Cayley graph with
  coset fibres. They include the Khot--Vishnoi instances and every folded
  long-code noise test. Established here: value equals transversal
  non-expansion; perfect completeness iff the walk acts freely on `G/K`; the
  symmetric SDP is a positive-definite-function problem; free-subgroup
  rounding with the duality "`H` free on `G/K` iff `K` free on `G/H`"; linear
  rounding over elementary abelian groups, tight on Khot--Vishnoi; an
  exponent-weighted version over every finite abelian group; subgroup-indicator
  certificates with permutable rounding.
  Artifacts: `research/artifacts/ugc-galois-games-2026-09-12.md` and
  `research/artifacts/ugc-galois-games-part2-2026-09-12.md`.
* **Open, sharpened.** `free-subgroup-rounding-is-universal-at-bounded-exponent`.
  For normal `K`, it asks whether a near-optimal positive-definite certificate
  vanishing on `K \ {e}` always yields a subgroup `L`, meeting `K` trivially,
  with `mu(L) >= 1 - C(m) eps log k`.

## 4. Search record

Web searches on 2026-09-12 covered: UGC and small-set expansion 2025 arXiv;
unique games on Cayley graphs with SoS (2024); SoS integrality gaps and the
2-to-2 theorem; 2-to-1/2-to-2 perfect completeness 2025--2026; unique games with
coboundary expansion and HDX (Bafna--Minzer 2025); SoS lower bounds via
Grigoriev--Tulsiani reductions. None surfaced a 2025--2026 proof or refutation of
UGC or SSEH, beyond the items above. That is a search-limited statement, not
evidence of absence. I did not locate a paper deriving SoS lower bounds at
completeness `1/2` from the 2-to-2 reduction. Whether such a transfer is recorded
in the literature was not settled.
