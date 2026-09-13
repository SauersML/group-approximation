# Novelty sweep: STW Problem L and the rotation summand

Lane `l-novelty`, 2026-09-13, main tip `25cb3f111`. This addendum does the arXiv listing step that
`research/artifacts/fz-stw-l-review-2026-09-13.md` §6 left undone. It also rechecks the sources of that section.

## Verdict: NOVEL-AS-FAR-AS-SEARCHED

The verdict covers two targets.

- **L-K**, the Kirchberg disjunct of STW Problem L (arXiv:2506.10902v2, §14, TeX label `q:pi1`): find explicit loops
  that generate π_1(Aut(A)) ≅ ℤ⁶, where A is the unital UCT Kirchberg algebra with the K-theory of A_θ.
- **LS**, the request printed just before Problem L: prove that the two rotation loops span a ℤ² direct summand.

The answers under check are:

- for L-K, node `stw50-kirchberg-kernel-loops-proof` and `research/artifacts/stw50-six-kirchberg-loops-2026-09-05.md`;
- for LS, node `stw50-rotation-loops-form-a-direct-summand` and
  `research/artifacts/stw50-rotation-loop-retraction-2026-09-04.md`.

No source found through 2026-09-13 gives six explicit generating loops for this K-theory. None proves the ℤ² summand,
either for A_θ or for A_θ ⊗ O_∞. The search is bounded, so it does not prove absence. §5 lists the credit risks and
§6 what the search could not reach. The stably finite disjunct of Problem L is not claimed here.

## 1. The printed text

The STW v2 TeX e-print was read in the session scratchpad and not committed (source lines 1204–1232). It says:

- Dadarlat's identification π_k(Aut(A)) ≅ KK¹(C_uA, S^kA) is abstract, via Kirchberg–Phillips classification of
  maps A → C(S^k, A).
- For k = 1 and O_n, the gauge action gives the generating loop. STW call this one of few explicit cases.
- Work in progress of Gabe and Schafhauser computes π_k(Aut(A)) for unital finite classifiable A, so
  π_1(Aut(A_θ)) ≅ ℤ⁶.
- The rotation action gives two loops, detected by winding numbers. STW write "we strongly suspect these loops define
  a $\mathbb Z^2$ direct summand". They would welcome a proof, and say the source of the other four generators is
  unclear.
- The same question is raised for γ ⊗ id on A_θ ⊗ O_∞.
- Problem L itself, followed by the "more generally" request for other UCT Kirchberg or monotracial algebras.
- A remark points to groupoid models and, in the Kirchberg case, Cuntz–Krieger models.

Versions: v1 is dated 12 Jun 2025 and v2 8 May 2026, with no v3 on 09-13. The v2 comment says it will appear in a
Münster J. Math. special issue in memory of Eberhard Kirchberg.

## 2. Sources, endpoints and failures

All checks ran on 2026-09-13. The first pass ran 13:55–14:05 UTC; a second arXiv search pass ran while landing.

| Source | Endpoint | Status |
|---|---|---|
| arXiv export API | `export.arxiv.org/api/query`, http and https | body `Rate exceeded.` or empty, 0 entries: unusable |
| arXiv search | `arxiv.org/search`, `/search/advanced`, title and abstract metadata | worked |
| arXiv pages | `arxiv.org/abs/<id>`, `/html/<id>`, `/e-print/2506.10902v2` | worked; html view omitted §14, so read TeX |
| Semantic Scholar | `/graph/v1/paper/<id>/citations` by web fetch | worked for 2506.10902, 10.4171/jncg/3, 2404.06115 |
| Semantic Scholar | the same for 2502.18126; `/paper/search` by curl | HTTP 429 |
| OpenAlex | `api.openalex.org/works`, `filter=doi:` and `cites:` | worked |
| Web search | 11 queries, §3.5 | worked |
| Author pages | `sites.google.com/view/cschafhauser`, `sites.google.com/view/tarosogabe` | worked |

Gabe's research page was checked by the review and not again here. No PDF was downloaded into the repository.

## 3. Query log

### 3.1 Papers citing arXiv:2506.10902

- **Semantic Scholar**: 9 records for 8 distinct papers: arXiv 2609.11297, 2609.08892, 2607.04300, 2602.10616
  (Proc. London Math. Soc., doi 10.1112/plms.70180), 2601.23029, 2601.08779, 2508.07938 and 2508.04837.
- **OpenAlex**: the STW record W4417357163 has 0 indexed citers.
- **Screen**: the topics include selflessness, stable rank, topological full groups and embeddings into II_1
  factors. None studies loops in automorphism groups, automorphisms of rotation algebras or Problem L.

### 3.2 Dadarlat 2007 and its citers

The source is M. Dadarlat, "The homotopy groups of the automorphism group of Kirchberg algebras", J. Noncommut. Geom.
1 (2007), 113–139, doi 10.4171/jncg/3. OpenAlex `cites:` gave 25 records and Semantic Scholar 32. All titles were
screened. The first three rows below had their abstracts read; the other rows were screened by title.

| Item | Content | Loops for K_*(A_θ) or the summand? |
|---|---|---|
| arXiv:1810.05849, a weak homotopy equivalence type result related to Kirchberg algebras | homotopy type of Aut | no |
| arXiv:1903.02796 (2019) | abstract read | no |
| arXiv:1903.04809, group structure of homotopy sets with target Aut(O_n) | O_n only | no |
| Cuntz–Toeplitz algebras, J. Math. Soc. Japan, doi 10.2969/jmsj/82338233 | title screened | no |
| Poly-ℤ actions on Kirchberg algebras II, arXiv:1906.03818 | classification of actions | no |
| continuous fields of Cuntz algebras, arXiv:2010.00750 and part I | field invariants | no |
| reciprocal Kirchberg algebras, arXiv:2204.11199 (J. Funct. Anal. 2024) | reciprocal constructions | no |
| arXiv:0704.0583, KK-theory of strongly self-absorbing algebras | not about Aut loops | no |

### 3.3 The Matsumoto–Sogabe line and nearby papers

- **arXiv:2404.06115**, on the homotopy groups of the automorphism groups of Cuntz–Krieger algebras (J. Noncommut.
  Geom., doi 10.4171/jncg/598). It computes these groups "in terms of the underlying matrices". It gives no loop
  formulas, treats no tensor products and does not mention Problem L.
  - Semantic Scholar citers (4): 2511.06760, 2502.18126, 2408.09359, 2405.03204.
  - OpenAlex citers (2): a 2025 book chapter on K-theory for Cuntz–Krieger algebras and a 2025 paper on λ-graph
    systems.
- **arXiv:2502.18126**, reciprocal Cuntz–Krieger algebras. By the review, §7 Theorem 7.1 gives an isomorphism
  π_1(Aut(O_A)) → π_1(Aut(Ô_A)) that sends the gauge class to the gauge class. It names one loop and no basis.
  OpenAlex shows 0 citers, and Semantic Scholar could not be reached.
- **arXiv:2408.09359**, total extension groups for unital Kirchberg algebras: no loops or generator formulas.
- **arXiv:2511.06760**, universal property of reciprocal Kirchberg algebras: no loops.
- **arXiv:2405.03204**: title screened, not on loops.
- **arXiv:2606.09212** (Kamikawa): equivariant homotopy groups of Aut via equivariant Dadarlat–Pennig theory. Abstract
  KK identifications, no explicit loops, and it does not cite STW.
- **arXiv:2607.16755** (Sogabe, 18 Jul 2026): inner automorphism groups of Cuntz algebras have the homotopy groups of
  Aut. No loops for this K-theory.
- **arXiv:2607.20105** (Pennig–Tridimas, 22 Jul 2026): no loops.
- **Sogabe's homepage**: 12 papers, none with explicit loops or rotation algebras. "Kirchberg algebras with the same
  homotopy groups of their automorphism groups" appears only as a talk title.
- **Schafhauser's homepage**: no paper on homotopy groups of Aut or on loops.

### 3.4 arXiv metadata searches

Cross-lists are included. The relevant column lists the hits that could bear on L-K or LS.

| Query | Dates | Results | Relevant |
|---|---|---|---|
| abstract `automorphism group homotopy` | all | 153, 150 listed | only §3.2–3.3 items and 2511.14541; no loops |
| abstract `Kirchberg` AND `automorphism` | all | 20 | 2606.09212, 2408.09359, 1810.05849; no loops |
| abstract `Kirchberg` AND `homotopy` | all | 7 | adds 2505.04857 and 2202.09809; no loops |
| abstract `loops` AND `automorphism` AND `K-theory` | all | 9 | bundles of strongly self-absorbing algebras; no rotation or Kirchberg loops |
| abstract `rotation algebra` AND `automorphism` | 2025-06-01 to 2026-09-13 | 6 | none on Aut homotopy |
| abstract `rotation algebra` AND `"fundamental group"` | all | 4 | none in math.OA |
| abstract `"fundamental group"` AND `"automorphism group"` AND `C*-algebra` | all | 0 | none |
| abstract `irrational rotation` AND `homotopy` | all | 1 | not on Aut loops |
| abstract `"direct summand"` AND `"automorphism group"` AND `homotopy` | all | 0 | none |

The export API attempts covered the same families, plus Problem L by name. All were rate-limited.

### 3.5 Web searches

Each query below returned nothing that gives loops for this K-theory or a proof of the summand.

1. `"Problem L" Schafhauser Tikuisis White loops automorphism group rotation algebra`
2. `explicit generators fundamental group automorphism group Kirchberg algebra loops arXiv 2026`
3. `Gabe Schafhauser homotopy groups automorphism group classifiable C*-algebras rotation algebra preprint`
4. `"fundamental group" "automorphism group" "irrational rotation algebra" homotopy Z^6 loops generators`
5. `graph C*-algebra edge gauge action loop automorphism group KK class Dadarlat homotopy groups Cuntz-Krieger algebras`
6. `"generalized gauge action" OR "quasi-free action" fundamental group automorphism group Cuntz-Krieger algebra
   generators loops`
7. `"direct summand" rotation action "automorphism group" irrational rotation algebra fundamental group winding Bott
   trace`
8. `loops of automorphisms Kirchberg algebra circle actions tensor product graph algebras KK(A,SA) explicit basis 2025
   2026 math.OA`
9. `"homotopy groups" "automorphism groups" "classifiable C*-algebras" Gabe Schafhauser 2026 arXiv`
10. `"99 problems" Schafhauser Tikuisis White problem solved answer arXiv 2026 automorphism loops "Problem L"`
11. `"Kirchberg algebras with the same homotopy groups of their automorphism groups" arXiv`

## 4. Findings

- The nearest printed results are in the Cuntz–Krieger line (§3.3). They compute π_1(Aut(O_A)) abstractly from the
  matrix, and 2502.18126 tracks the gauge class. None gives a basis of loops for a group of rank above one. None
  treats K_*(A_θ), a tensor product of graph algebras, or the rotation action.
- No source proves or refutes that the rotation loops span a ℤ² summand, for A_θ or for A_θ ⊗ O_∞.
- STW v2, dated 8 May 2026, still poses both requests. No citer of STW up to 09-13 answers them.

## 5. Credit risks

1. **Gabe–Schafhauser work in progress.** It is unpublished, and STW cite it for the stably finite computation. It
   may contain loops or the summand for A_θ. It is the likeliest competing answer. Priority wording on LS should be
   modest until it appears.
2. **The gauge-loop tradition.** Circle actions by edge phases on graph algebras are standard generalized gauge
   actions. Matsumoto–Sogabe already compute π_1(Aut(O_A)) from the matrix. Experts may call individual edge-phase
   loops folklore. Per §8 of the six-loops artifact, the contribution is the specific graphs, rows and assembly.
3. **Standard tools in the summand proof.** Bott periodicity, Pimsner–Voiculescu, trace and evaluation are routine.
   Experts may call LS easy once asked, even though STW print it as a request.
4. **Non-explicit identifications.** ψ and χ come from Kirchberg–Phillips existence. The loops are explicit on the
   models, but they reach A through isomorphisms that are not constructed. A referee may say this falls short of
   "explicit" in Problem L (review §7). No single presentation displays all six loops.
5. **Search limits** (§6).

## 6. What this search could not reach

- **arXiv listing.** No date-ordered math.OA listing sweep: the export API was rate-limited. arXiv search covers only
  title and abstract metadata, not full text.
- **Citation databases.** No MathSciNet, zbMATH or Google Scholar citation data. The Semantic Scholar citers of
  2502.18126 were not reached.
- **Depth of screening.** Most citers were screened by title only; abstracts were read only for the items in
  §3.2–3.3.
- **Unindexed work.** Unposted work, talks, theses, and journal papers without arXiv records can be missed. So can a
  paper that answers Problem L without citing STW or Dadarlat and without the searched words.

## 7. Addendum to the review, §6

The review's "Not done" item is now done within the limits of §6. arXiv search listings, not the export API, were
swept for nine query families, most over all dates. The new items seen are 1810.05849, 1903.02796, 1903.04809,
2405.03204, 2408.09359, 2505.04857, 2607.20105 and the Cuntz–Toeplitz paper. None changes the review's conclusion:
no explicit six-loop basis was found, and no other answer to either disjunct of Problem L or to LS.
