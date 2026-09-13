# Open status and statement audit of the EX swarm targets (2026-09-12)

Lane `ex-novelty`, 21:40–22:10 CDT. Cairn read at main `3bf9dea0d`.

## Method, and how far it reaches

For every target I read the Cairn root on main and compared its statement with the source it cites.
Then I ran a bounded freshness check:
- 1–3 WebSearch queries per target;
- a WebFetch of the arXiv abstract or full text of every 2026 paper that surfaced as a possible
  threat.

The planned arXiv API batch on MSI (37 phrase queries, newest 25 each) got empty responses from the
node and contributes nothing yet (last section).

Evidence tags:
- **P**: primary text fetched in this session (abstract or full text).
- **C**: quoted from a primary source inside the Cairn node by an earlier lane (not re-read here).
- **W**: web-search summary only, not a primary reading.

"OPEN" below means that no resolution turned up within this bound. It does not prove that none exists.

**Global threat check.** The ten results OpenAI announced on 2026-08-01 (secondary source: kingy.ai,
"OpenAI Astra's 10 Math Results"):
1. the sphere-packing LP ceiling;
2. code bounds;
3. existence of a nonsofic group;
4. the Connes rigidity conjecture, negatively;
5. permanent lower bounds;
6. exponential parallel repetition for entangled games;
7. GapCVP hardness;
8. an Ehrhart volume inequality;
9. multicolour triangle Ramsey growth;
10. the compactness and degeneracy conjectures, negatively.

Only the nonsofic group touches this swarm, and it is an input. Parallel repetition for entangled
games is adjacent to the games form of quantum PCP, not to its Hamiltonian form.

## Table

| # | Target | Lanes | Cairn root | Status 2026-09-12 | Bound |
|---|---|---|---|---|---|
| 1 | Pestov Q3.4: hyperlinear ⇒ sofic? | ex-q34-leavitt-hs, ex-q34-kt-double, ex-q34-collapse | `hyperlinear-nonsofic-group`, `hyperlinear-implies-sofic` | OPEN | 3 W, 3 P |
| 2 | a non-hyperlinear group | ex-nh-mipstar, ex-nh-fresh | `non-hyperlinear-group` | OPEN | 2 W |
| 3 | f.p. infinite simple sofic or hyperlinear group | ex-fp-simple-sofic | `hyperlinear-fp-infinite-simple-group` | OPEN, source of question unrecorded | 2 W, 1 P |
| 4 | Pestov 9.1: simple Kazhdan hyperlinear group | ex-kazhdan-simple-hyperlinear | `infinite-simple-kazhdan-hyperlinear-group` | OPEN | 2 W |
| 5 | left-orderable nonsofic group | ex-left-orderable-nonsofic | `left-orderable-non-sofic-group` | OPEN, source of question unrecorded | 1 W, 2 P |
| 6 | soficity of Thompson's V | ex-thompson-v-soficity | `thompson-v-is-sofic`, `thompson-v-not-sofic` | OPEN | 1 W, 1 P |
| 7 | a non-weakly-sofic group (Glebsky–Rivera) | ex-weak-soficity | no claim root; artifact `non-weakly-sofic-group.md` | OPEN | 1 W |
| 8 | Bernoulli entropy classification, all groups | ex-bernoulli-negative, ex-bernoulli-positive | `bernoulli-shift-entropy-classifies-for-every-group` | OPEN | 1 W |
| 9 | positive Rokhlin entropy, all groups | ex-rokhlin-lower | `every-group-has-positive-rokhlin-entropy-action` | OPEN | 1 W |
| 10 | nonsofic free action of a sofic group; SL3(Z) | ex-nonsofic-action-relative, ex-nonsofic-action-entropy | `sl3z-admits-nonsofic-action`, `mixing-free-nonsofic-action-of-sofic-group` | general case SOLVED (Kun–Thom); SL3(Z) and mixing OPEN | 1 W, 1 P |
| 11 | determinant conjecture counterexample | ex-determinant-monster | `determinant-conjecture` | OPEN | 1 W |
| 12 | Lück approximation beyond sofic | ex-lueck-approximation | none on main | OPEN | 1 W |
| 13 | Strong Atiyah, torsion-free | ex-atiyah-torsion-free | `strong-atiyah-torsion-free` | OPEN | 1 W |
| 14 | STW XXIII, Rank Problem | ex-rank-problem-villadsen, ex-rank-problem-lix | `stw99-problem-xxiii-rank-problem` | OPEN | 1 W, 1 P |
| 15 | STW LXI, properly infinite ⇒ K1-injective | ex-k1-properly-infinite | `stw99-problem-lxi-properly-infinite-k1-injective` | OPEN per STW v2; disputed preprint | 1 W |
| 16 | Toms–Winter | ex-toms-winter | `stw99-problem-xviii-toms-winter-conjecture` | OPEN | 1 W |
| 17 | UCT | ex-uct | `stw99-problem-ii-nuclear-uct` | OPEN | 1 W |
| 18 | MF reduced C*-algebra of an infinite (T) group | ex-mf-kazhdan-cstar | `infinite-kazhdan-group-with-mf-reduced-cstar` | OPEN; genuine-rep strong convergence dead for SL_d(Z), d ≥ 4 | 2 W, 1 P |
| 19 | Blackadar–Kirchberg | ex-blackadar-kirchberg | `stw99-problem-vii-blackadar-kirchberg` | OPEN | 1 W |
| 20 | Rørdam's real rank zero dichotomy | ex-rr0-dichotomy | `stw99-problem-xxix-rr0-dichotomy` | OPEN | 1 W |
| 21 | simple C*-algebra, unitary component group of class ≥ 3 | ex-unitary-class-three | `simple-cstar-unitary-components-class-three` | no example found; repo-generated question | 2 P |
| 22 | hyperbolic groups virtually torsion-free | ex-hyperbolic-vtf | `hyperbolic-groups-virtually-torsion-free` | OPEN | 1 W |
| 23 | Baum–Connes, trivial coefficients | ex-baum-connes | `baum-connes-counterexample-group-exists` | OPEN | 1 W |
| 24 | Kadison–Kaplansky, torsion-free | ex-kadison-kaplansky | `kadison-kaplansky-torsion-free` | OPEN | 1 W |
| 25 | Π⁰₂-completeness of soficity / amenability, f.p. | ex-complexity-sofic, ex-complexity-amenable | `sofic-recognition-finite-presentations-is-pi2-complete`, `amenability-of-finite-presentations-is-pi2-complete` | OPEN; repo-generated framing | 1 W |
| 26 | f.p. simple groups, arbitrarily complex word problem | ex-complexity-amenable | `fp-simple-groups-with-arbitrarily-complex-word-problem` | OPEN | 2 W |
| 27 | Unique Games Conjecture | ex-ugc | `unique-games-conjecture` | OPEN | 1 W |
| 28 | quantum PCP, Hamiltonian form | ex-quantum-pcp | `quantum-pcp-constant-gap-local-hamiltonian` | OPEN | 1 W |

## Evidence per row

1. Pestov arXiv:0804.3968 Q3.4, matching the node (C).
   - Nonsofic groups now exist: OpenAI (announced 2026-08-01), Kun–Thom arXiv:2608.06222 and
     Fournier-Facio arXiv:2608.02025. None is shown hyperlinear or non-hyperlinear.
   - The Fournier-Facio v1 full text never mentions hyperlinearity (P). The Kun–Thom abstract does
     not mention it either (P).
   - Web summaries repeat that the hyperlinearity of all three is open (W).
2. MIP*=RE yields a non-embeddable II_1 factor but no group. The nearest 2025 objects are not groups:
   - an equivalence relation whose von Neumann algebra is not Connes embeddable (arXiv:2502.06697,
     title only, W);
   - IRSs of free groups that are not co-hyperlinear (arXiv:2508.15154, W).
3. The strengthening "sofic" is the node's preferred form.
   - The companion artifact `fp-simple-amenable-full-groups-2026-09-12.md` found no written source for
     the amenable version (C).
   - Every recorded f.p. infinite simple group lacks an approximation certificate. The node explains
     why: none is RF or LEF.
   - Ersoy arXiv:2604.19174 (2026-04-21) only proves conditional structure theorems for minimal
     nonsofic groups and names no group (P).
4. Verbatim in the node, from Pestov's PDF p. 21: "Open question 9.1 (Cf. Ozawa [64]). Let G be an
   infinite simple group with Kazhdan's property (T). Can it be hyperlinear (sofic)?" (C). The web search
   returns only the question itself (W).
5. No literature source is recorded; the node is a group-property atlas cell (C).
   - The Fournier-Facio v1 full text never mentions orderability or local indicability (P).
   - The Kun–Thom abstract does not either (P).
   - Left-orderability forces torsion-freeness, which leaves the Fournier-Facio family as the natural
     test case.
6. The web search found no resolution (W). Ersoy 2604.19174 names no group (P). OpenAI's construction
   uses V as an ingredient but does not decide V.
7. The artifact states Glebsky–Rivera Conjecture 4.5, arXiv:0709.0026 (C).
   - The web still lists it open; the latest permanence result is Glebsky arXiv:1910.08631 (W).
   - `kun-thom-clifford-cover-weakly-sofic` records a weakly sofic nonsofic group, so no nonsofic
     result carries over.
   - The lane has to author or restore a claim root.
8. The node quotes Seward arXiv:1805.08279 verbatim: "If non-sofic countable groups G exist, then it
   is still unknown whether (2^G,u_2^G) and (3^G,u_3^G) are isomorphic." (C) The web found no
   resolution (W).
9. The node quotes the abstract of Seward arXiv:1501.03367 (C). Its `refuted_by:
   leavitt-unit-group-nonsurjunctive` points at an OPEN claim. That is a structural link, not a
   refutation.
10. Păunescu's question (arXiv:1002.0605) is answered negatively in general.
    - Kun–Thom arXiv:2608.06222 (v1 2026-08-06, v3 2026-08-20; P) prove in Corollary 3.2 that an
      infranormal non-normal Kazhdan pair Γ < G gives G a free, strongly ergodic, nonsofic action.
    - The pair EL_r(F_q[x]) < EL_r(F_q[x^±]) ⋊ SL_d(Z) is residually finite.
    - In Cairn this is `kun-thom-free-nonsofic-action` (ESTABLISHED, C), which refutes
      `sofic-groups-in-paunescu-sofic-action-class`.
    - Open: SL3(Z), where no infranormal non-normal Kazhdan pair is known, and mixing actions.
    - Both lanes were messaged at 22:00.
11. The node matches Lück (2002), Ch. 13 (C). The conjecture holds for sofic groups (Elek–Szabó 2005).
    arXiv:2508.15154 extends it to IRSs and exhibits a non-co-hyperlinear IRS that satisfies it (W).
    So nonsoficity alone does not produce a counterexample.
12. Title grep found no root. The approximation is known for sofic approximations (Elek–Szabó;
    Jaikin-Zapirain over Q̄), and the determinant conjecture feeds approximation (Schick; W). This lane
    shares cruxes with ex-determinant-monster.
13. arXiv:2606.19606 (2026) surveys the known classes (W; Cairn cites it as Fisher–Ng). Known
    counterexamples all have torsion.
14. The node matches STW arXiv:2506.10902 Problem XXIII (C). STW v2 is dated 2026-05-08 (P, submission
    history). Known cases: stable rank one (Thiel) and nowhere scattered stable rank one (APRT). The web
    finds nothing newer (W).
15. Blanchard arXiv:1606.04773 claims that T_2 *_C T_2 is properly infinite and not K1-injective.
    - The Cairn artifact `stw61-blanchard-preprint-firewall-2026-08-30.md` finds a gap in the
      non-null-homotopy step (C). STW v2 still lists LXI.
    - CREDIT: any result about that algebra or O_∞ * O_∞ must cite Blanchard and Blanchard–Rohde–Rørdam.
16. The last implication, strict comparison ⇒ Z-stability, is still open in general (W).
17. No counterexample and no proof turned up (W). The reductions (Kirchberg, Barlak–Li, Dadarlat) are in
    Cairn.
18. Magee–de la Salle arXiv:2312.03220 (C. R. Math. 362, 2024).
    - Every finite-dimensional unitary representation of SL_4(Z) has an SL_2(Z)-invariant vector, so
      SL_d(Z) is not purely MF for d ≥ 4.
    - SL_3(Z) is open, and approximate models are not excluded (W, C).
    - The 2026 MF/PFF sources: Gao–Kunnawalkam Elayavalli–Manzoor–Patchell arXiv:2603.24502 (P: no (T)
      groups) and arXiv:2603.13564 (W).
19. The problem has an affirmative answer for simple UCT algebras (Tikuisis–White–Winter). The web
    finds nothing newer (W).
20. The node matches STW XXIX, from Rørdam, Acta 2003, Question 7.6 (C, W). No 2026 development turned
    up (W).
21. The question is repo-generated and extends the class-two examples.
    - Toms arXiv:2609.09535 (2026-09-08), main theorem (P): "There exists a simple, separable, unital,
      infinite-dimensional, nuclear AH algebra A such that K₁(A)=0 and 𝒰(A)/𝒰₀(A) contains a nonzero
      element of order two."
    - Its text has no commutator or nilpotency statement (P).
    - CREDIT: Toms has priority on the first simple non-K1-injective algebra.
22. The node matches Lück 2008 Problem 11.1(i) (C). Non-virtually-torsion-free examples exist only in
    wider classes (W):
    - Hughes arXiv:2105.02847 (hierarchically hyperbolic lattices);
    - Kropholler–Vankov arXiv:2007.13880.
23. Counterexamples are known only with coefficients (Higson–Lafforgue–Skandalis) (W).
24. No counterexample turned up. The algebraic neighbour, the unit conjecture, was refuted by Gardam in
    2021 (W).
25. Main records only the unconditional placements Π⁰₂ \ Π⁰₁ (`*-arithmetical-position`). The web found
    no completeness result (W).
26. It is stated as a consequence of Boone–Higman (W). Boone–Higman itself remains open (survey
    arXiv:2306.16356v3, May 2025; W). The survey text was not checked for this corollary.
27. The 2-to-2 theorem (2018) is still the frontier (W).
28. No resolution turned up (W). See the games-version survey arXiv:2403.13084, and Astra's parallel
    repetition result (adjacent).

## Priority notes found in passing

- Eckhardt, arXiv:2608.28772 (2026-08-28; P).
  - Setting: Γ has property (T) and an injective non-surjective endomorphism, and G is the associated
    ascending HNN extension.
  - Result: W = (⊕_{G/Γ} Z/2) ⋊ G is not MF, and C*(G) is not finite.
  - The paper says the ideas and proofs came from ChatGPT 5.6 Sol.
  - This is the compression-plus-rigidity pattern behind the repo's non-MF results. It is already recorded
    on main: `non_mf_groups_exist.tex` cites it, and `research/artifacts/non-mf-without-property-t.md`
    discusses it. No new credit action is needed.
- Toms arXiv:2609.09535 answers STW LIX negatively. It predates our public LIX results.
- OpenAI's announced counterexample to Connes rigidity: mutually commensurable property (T) groups with
  the same group von Neumann algebra (secondary source).

## arXiv API batch

The script `run.sh` (37 phrase queries, newest 25 each, 3 s apart) ran on MSI, and every response was
empty. A diagnostic request at 22:08 returned HTTP 429 from `export.arxiv.org/api/query`: the shared node
is rate limited. `arxiv.org/abs/...` answered 200. The table therefore rests on WebSearch plus the primary
fetches above. A slower rerun of the highest-value queries will be appended here.
