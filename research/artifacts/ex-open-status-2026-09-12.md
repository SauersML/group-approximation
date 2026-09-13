# Open status and statement audit of the EX swarm targets (2026-09-12)

Lane `ex-novelty`, 21:40–22:10 CDT. Cairn read at main `3bf9dea0d`.

## Method, and how far it reaches

For every target I read the Cairn root on main and compared its statement with the source it cites.
Then I ran a bounded freshness check:
- 1–3 WebSearch queries per target;
- a WebFetch of the arXiv abstract or full text of every 2026 paper that surfaced as a possible
  threat.

The arXiv export API was rate limited (HTTP 429), so the planned 37-query batch on MSI returned nothing.
The arxiv.org search UI stood in for it; see "arXiv listing check" below. No listing contradicts any OPEN
row.

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
| 4 | Pestov 9.1: simple Kazhdan hyperlinear group | ex-kazhdan-simple-hyperlinear | `infinite-simple-kazhdan-hyperlinear-group` | ANSWERED on main by EL_3(LC(X,F_q) ⋊ Z)/Z (established 8b65f0932; review PASS 0efeac4106); deep pass found no earlier answer | 12 S + 369 T (see verdict section) |
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
| 21 | simple C*-algebra, unitary component group of class ≥ 3 | ex-unitary-class-three | `simple-cstar-unitary-components-class-three` | no literature example; lane claims one at 22:28 (4edaed478a), unreviewed | 2 P |
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

## Pestov 9.1 verdict (23:50)

- **(a) The question.** Verbatim from arXiv:0804.3968v8, p. 21 (the galley-corrected BSL version): "Let G be
  an infinite simple group with Kazhdan's property (T). Can it be hyperlinear (sofic)?" It does not ask for LEF.
- **(b) Earlier examples.** No earlier infinite simple sofic, hyperlinear or LEF Kazhdan group was found.
  - Sources: 12 LaTeX sources, among them Pestov–Kwiatkowska 2009 (which still calls it open), Capraro–Lupini
    2015 (silent), Thom's ICM survey, the EJZK memoir and Alekseev–Thom's Aug 2026 list of known examples.
  - Plus 369 OpenAlex citing titles.
- **The tension.** Dadarlat 2007.12655v2 prints "MF ⇒ weak quasidiagonality" as clear from the definitions.
  Together with his remark that infinite simple (T) groups are not weakly QD, that would forbid S. The
  definitions give the reverse arrow, so S refutes the printed sentence.
- **(c) EKL2.** It is repository-internal (`exact-kazhdan-radical-kernel-cannot-be-lef`) and marked false on
  main. No earlier LEF Kazhdan group without finite quotients was found.
- Details and bounds: `research/artifacts/ex-novelty-pestov91-deep-pass-2026-09-12.md`.

## RF_fp and LEF_fp Π⁰₂-completeness verdict (2026-09-13, 00:45)

- **Novelty.** No earlier completeness result was found. The nearest printed results are partial:
  - RF_fp is not c.e. (Rauzy arXiv:2111.01190);
  - a nontrivial finite quotient is undecidable (Bridson–Wilton 1401.2273);
  - residual finiteness is boldface Π⁰₃-complete on marked groups (Rauzy 2605.30138).
  KMS prove only "sym-universally halting ⇒ G(M) is RF".
- **Framing.** The question is not printed as such. KMS §1.1.7 asks the residually finite Higman embedding question
  instead, and Rauzy arXiv:2002.02540 answered that negatively. So `rf-higman-embedding-for-decidable-groups` is stale
  on main.
- Details: `research/artifacts/ex-novelty-rf-fp-pi02-pass-2026-09-13.md`.

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

## Novelty and priority log of EX landings

Entries come from `state/landed.log`. A check is bounded as stated in each entry.

- **21:43 / 21:49 / 21:55, ex-verify-groups, ex-verify-analysis** (f6ec096b31, ce22376c2d, 61fb2b2a65):
  review artifacts. They make no new theorem claims.
- **21:54, ex-kadison-kaplansky, b2c98f0e30.** `fractional-matrix-trace-gives-projection-in-g-star-z`,
  Corollary A: Kadison–Kaplansky for all torsion-free groups ⇔ integral trace on K_0 for all
  torsion-free groups, through strict comparison in C*_r(G * Z).
  - The credit paragraph is present:
    - Dykema–Rørdam, GAFA 8 (1998), nuclear factors;
    - Flores–Klisse–Ó Cobhthaigh–Pagliero arXiv:2510.24675 (selflessness);
    - Robert arXiv:2309.14188.
  - I added one web search, which found no prior statement of Corollary A.
  - The neighbouring paper Dykema–Rørdam II (Math. Z. 234 (2000); abstract P) treats reduced free
    products of infinitely many factors: K_0 is determined by K_0(φ) when φ is a trace. It does not
    state Corollary A.
  - Verdict: packaging of known theorems with a new consequence; novelty unverified; no priority
    threat found.
- **21:59, ex-fp-simple-sofic, 1da285e701.**
  - `amenable-orbit-full-group-subgroups-are-sofic` is folklore and correctly credited (Elek–Szabó;
    Elek arXiv:1211.0621).
  - `kazhdan-subgroups-of-amenable-orbit-full-groups-are-rf` carries no credit line. Its main theorem
    follows from two classical facts:
    - (T) ⇒ strong ergodicity (K. Schmidt, ETDS 1 (1981); Connes–Weiss 1980);
    - infinite ergodic hyperfinite relations are not strongly ergodic.
    Theorem numbers were not re-read. The lane was messaged at 22:25.
  - Ma arXiv:2209.00580 Theorem C, read verbatim (P): "Let α:G↷X be a minimal topologically free
    residually finite action of a countable discrete group on the Cantor set. Then [[α]] is LEF and
    thus sofic." "Residually finite action" is Kerr–Nowak's notion.
  - The lane's `sfts-without-finite-orbits-are-not-residually-finite-actions` shows that Z^2 acting on
    Labbé's shift is not such an action. So Ma gives no LEF refutation of the open
    `labbe-shift-derived-full-group-is-finitely-presented`.

- **22:04, ex-baum-connes, 996c78f231.**
  - The dead route `bc-counterexample-via-ghost-projection` has `requires: []`. It is killed by the
    established `reduced-group-algebras-contain-no-nonzero-ghosts`, which carries `invalidates:` and a
    proof route. Checked: it does not fire.
  - Context: Tian–Yu arXiv:2605.12930 (rev. 2026-08-20; abstract P) show that the Kun–Thom nonsofic
    groups have Property A. So any trivial-coefficient failure on those groups has to be a failure of
    surjectivity. The injectivity step (coarse embeddability) was not re-read.
- **22:04, ex-rr0-dichotomy, b82fcb23ef.** Three citation imports (Ara–Goodearl; Ortega–Perera–Rørdam,
  two nodes). No new theorem. I did not check them against the sources.
- **22:05, ex-nh-mipstar, 9eb255abc3.**
  - `qc-qa-graph-gap-gives-non-ce-quantum-automorphism-group` credits BCEHPSW Remark 4.3.
  - The correspondence it rests on is Lupini–Mančinska–Roberson arXiv:1712.01820 (abstract P): two
    connected graphs are quantum isomorphic iff Qut(X ⊔ Y) has an orbit meeting both. It is not cited.
    The lane was messaged at 22:35.
  - The open claims (a qc- but not qa-isomorphic pair, a non-CE Qut of a finite graph) match the bounded
    listings: none found.
- **22:06, ex-free-objects, 0f2758222e.** A computational presentation artifact for St_5. No
  novelty claim.
- **22:06, ex-rank-problem-villadsen, 814a8a6eb5.** `all-ranks-occur-iff-continuous-ranks-are-dense`
  has no credit line.
  - (1)⇔(2) is the standard passage from lower semicontinuous affine functions to increasing suprema of
    continuous ones (not source-checked).
  - One web search found no statement of (2)⇔(3).
  - Novelty unverified; low priority risk.
- **22:07, ex-weak-soficity, 13562b357e.** `residually-finite-doubles-are-weakly-sofic` credits Glebsky
  (Rev. Mat. Iberoam. 39 (2023)) plus Bass–Serre and calls the deduction immediate. Glebsky
  arXiv:1910.08631 (abstract P), "residually finite by residually finite extensions are weakly sofic",
  already suffices because the fold kernel is free. Credit is adequate.
- **22:07, ex-nonsofic-action-relative, db83b00ca5.** `howe-moore-lattice-nonsofic-action-transfers-to-mixing`
  (established, unreviewed).
  - Mechanism: induce to a Howe–Moore envelope, restrict to the lattice, then Păunescu Theorem 1.5.
  - The `sofic` listing contains no prior statement.
  - Worth an ex-verify pass: for such lattices it turns the mixing question into membership in
    Păunescu's class.

## arXiv listing check (arxiv.org search UI, newest first, 22:15–22:35)

The export API stayed rate limited: HTTP 429 from MSI and from WebFetch. The arxiv.org search UI answered.
The listings below are small-model summaries of the result pages (W), except where a paper's abstract
was fetched (P).

- `hyperlinear` (25):
  - No hyperlinear nonsofic group, no non-hyperlinear group, no hyperlinear simple Kazhdan or f.p. simple
    group.
  - Conditional items: Dogon–Vigdorovich arXiv:2506.20843 (rev. 2026-06-23; P) prove that flexible HS
    stability of SL_2(Z[1/p]) gives a non-hyperlinear finite central extension (credit context for
    ex-nh-*); 2604.01408 and 2507.22444 assume a non-hyperlinear group.
- `sofic` (50 newest, back to Dec 2024):
  - Nothing on V, a left-orderable nonsofic group, an f.p. simple sofic group, SL3(Z) actions, Bernoulli
    classification or Π⁰₂-completeness.
  - Context: Alekseev–Thom arXiv:2608.05362 (P) prove that a Kazhdan group with a sofic embedding whose
    centralizer acts ergodically is LEF, and residually finite if finitely presented. So an infinite f.p.
    simple sofic Kazhdan group (rows 3, 4) has no such embedding.
  - Tian–Yu arXiv:2605.12930 (row 23).
  - Aldous–Lyons II arXiv:2501.00173 (nonsofic unimodular networks).
  - Halo products arXiv:2601.18742 (rows 7, 10).
- `"weakly sofic"` (13): no non-weakly-sofic group; Glebsky–Rivera 0709.0026 is still the source.
- `"Rokhlin entropy"` (16): no universal positive-entropy or Bernoulli classification result; Seward
  1501.03367 is still conditional.
- `K_1-injective` (25): Toms 2609.09535 is the only relevant new paper. Nothing on LXI, class ≥ 3 or
  ranks.
- `"strict comparison"` (25): nothing settles XVIII, XXIII, XXIX, VII or II. Context: arXiv:2605.21655,
  "Divisibility and real rank zero" (row 20).
- `Toms-Winter` (2025–26): partial classes only.
  - arXiv:2604.24682: stable rank one plus tracial locally finite nuclear dimension ⇒ uniform Γ and
    Toms–Winter.
  - arXiv:2607.23817: subquadratic-growth ASH algebras.
  - arXiv:2511.02760: graph algebras.
  - These constrain where ex-toms-winter can look for a counterexample.
- `"universal coefficient theorem" nuclear` (2025–26): nothing on UCT or Blackadar–Kirchberg.
- `"virtually torsion-free"` (25): no non-virtually-torsion-free hyperbolic group; arXiv:2603.04612 is
  withdrawn.
- `"unique games conjecture"` (25 newest): all conditional or partial; see arXiv:2609.06775 (multilayered
  PCPs).
- `"quantum PCP"` (2025–26): arXiv:2608.16860 and 2608.16857 (adversarial fault tolerance toward
  circuit-to-Hamiltonian qPCP) and 2510.01333 (gap amplification). No resolution.
- `Baum-Connes counterexample` (2024–26): only coarse-variant and permanence results.
- `"Atiyah conjecture"` (2025–26): positive classes only (Out(G), arXiv:2606.19606; Coxeter groups,
  appendix of arXiv:2505.08701).
- `left-orderable sofic`: no results bearing on the question.

## arXiv API batch

The export API (37 queries, run on MSI) returned HTTP 429 throughout. The arxiv.org search UI and the
e-print sources stood in for it; see the listing section above and the Pestov 9.1 pass.
