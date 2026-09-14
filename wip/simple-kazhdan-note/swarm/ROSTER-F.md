# SK roster F: wave 8, doubling the swarm (~20:20)

User, 20:15: "u have barely any agents, let's double" / "to make manuscript even better" / "and better findings" / "higher impact" / "and simpler" / "and all credit and background lit properly attributed and mentioned".

State of play:
- Main's note: rev2 e80dcf20ad (5 pp, title "Infinite simple Kazhdan groups that are limits of finite simple groups").
- Rev3 is in assembly (sk-editor-3). It adds §2 "LEF groups": a f.g. group is LEF iff it is a subgroup of an infinite f.g. simple Kazhdan LEF group, via the lamplighter host plus a density patch. It also adds a universal host paragraph (Wilson).
- Always read the note with `git show "${T}:simple_kazhdan_sofic_group.tex"`, with braces. Scan `sk/state/landed.log` for "main" lines to see a new revision land.
- Decisions: `sk/drafts/rev2-decisions.md`, also on main as wip/simple-kazhdan-note/decisions.md.
- FALSE on main, never use:
  - diag(a,a^{-1},1) as a homomorphism;
  - the "double swap" γ ↦ (γ,γ^{-1}).
- Review queues: sk-verify-6 (literature, credit, paper-level lanes) and sk-verify-7 (mathematics lanes of this wave).

## Family L: credit and background literature (the user's explicit order)

### sk-lit-background
Write the background survey the note should rest on, with every reference verified through Crossref, publisher pages, or arXiv PDFs read on MSI. Areas:
- simple Kazhdan groups: Kazhdan; Gromov's random and hyperbolic monsters; Ol'shanskii; Caprace–Rémy; Ershov (golden groups); Titz Mite–Witzel;
- sofic and hyperlinear groups: Gromov; Weiss; Elek–Szabó; Rădulescu; Pestov; Capraro–Lupini;
- LEF: Vershik–Gordon, Gordon;
- topological full groups: Giordano–Putnam–Skau, Matui, Grigorchuk–Medynets, Juschenko–Monod;
- property (T) for EL_n over rings: Shalom, Vaserstein, Kassabov, Ershov–Jaikin-Zapirain, EJZ–Kassabov;
- normal structure of GL_n: Bass, Vaserstein, Suslin, Golubchik, Stepanov;
- crossed products and Steinberg algebras: Clark–Edie-Michell, Steinberg, BCFS, Nekrashevych;
- approximation questions: Ozawa, Brown, Pestov, Alekseev–Thom, Thom, Kun–Thom, Arzhantseva–Păunescu;
- expanders: Margulis, Lubotzky, Kassabov;
- embedding theorems: Higman, Wilson, Kionke–Schesler, Ore, Schupp.

Deliverable: `research/artifacts/sk-lit-background-2026-09-13-partK.md`. It must contain:
- a one-page draft background paragraph for the introduction, with verbatim-checked claims;
- verified bibitems (journal, volume, pages, DOI);
- a list of every place the note should cite something it does not cite now.

### sk-lit-credit-audit
Go through main's note sentence by sentence (rev2 now, and rev3 once it lands). For each sentence, decide whether it needs a citation it lacks, or credits the wrong source. Candidates to check:
- (T) ⇒ expanders (Margulis);
- Kazhdan's definition;
- ICC ⇒ II_1 factor (Murray–von Neumann);
- McDuff factors (McDuff);
- hyperlinear ⟺ L(G) ⊂ R^ω (Rădulescu, Ozawa Prop 7.1);
- transvections generate SL_d and PSL_d(F_2) is simple (Jordan, Dickson; any standard text);
- the Whitehead lemma;
- uniform recurrence of minimal systems (Gottschalk–Hedlund);
- bounded complexity ⇒ periodic (Morse–Hedlund 1938, Coven–Hedlund);
- Sturmian codings (Hedlund, Coven–Hedlund; Lothaire ch. 2);
- the continued-fraction degree fact (folklore);
- space of marked groups (Grigorchuk, Champetier);
- "LEF ⟺ marked limit of finite groups" (Vershik–Gordon; Stepin);
- Ore 1951; Kionke–Schesler; Wilson 1980.

Deliverable: a §6 proposal with verbatim before/after, verified bibitems, and the line cost.

### sk-lit-novelty-2
Make the novelty claims for rev3's new results bounded and precise:
- LEF iff subgroup of a simple Kazhdan LEF group;
- one simple Kazhdan LEF group containing every f.g. linear group;
- simple Kazhdan groups as marked limits of finite simple expanders.

Search for:
- "every countable group embeds in a simple group with (T)" (Ol'shanskii–Osin? Gromov's monsters? Belegradek–Osin?);
- simple hosts with approximation properties;
- LEF envelopes;
- earlier marked limits of finite simple groups with (T).

Deliverable: a novelty table (result → closest prior → difference → credit sentence) in `research/artifacts/sk-lit-novelty-2-2026-09-13.md`, plus the exact credit sentences for the note.

### sk-lit-locators
Check every theorem number, page and year in main's bibliography and text against the JOURNAL versions, not arXiv:
- Ozawa p. 527 and Proposition 7.1 (IJM 15 (2004));
- Pestov's BSL numbering (Example 4.5, Theorem 3.3, Open question 9.1);
- EJZ Theorem 1.1 (Invent. 179);
- Kirchberg Theorem 1.1 (Math. Ann. 299);
- Matui Lemma 3.4 and Theorem 4.9 (IJM 17);
- GM Theorem 2.6 (Sb. Math. 205);
- GMpres Theorem 1.1(3);
- Stepanov Theorem 4.4 (J. Math. Sci. 95);
- Kassabov (Invent. 170);
- GPS (Crelle 469);
- Alekseev–Thom 6.1;
- Vershik–Gordon pages;
- Morse–Hedlund.

Use publisher PDFs through MSI (curl with an institutional IP) and read the page images when text extraction fails. Deliverable: a table (VERIFIED / FIX) and bibitem replacements.

## Family H: higher impact findings

### sk-universal-lef-host-a and sk-universal-lef-host-b
Target: one infinite f.g. simple Kazhdan LEF group containing every f.g. LEF group with solvable word problem (or every recursively presented f.g. LEF group). The sharp analog of sk-strong-1/3 for LEF.
- Start (a): a LEF analog of Wilson's theorem, i.e. countable LEF groups inside 2-generator LEF groups, then the lamplighter host.
- Start (b): a direct universal construction, e.g. the lamplighter host over a single "universal" f.g. LEF group assembled from all finite models.

Record the sharpness: no countable group contains all f.g. LEF groups, by counting.

### sk-wp-host
A host with SOLVABLE word problem containing every f.p. residually finite group (sk-strong-3's next target): a computable Wilson overgroup plus computable Toeplitz models. Coordinate with sk-wp-embedding by name if needed.

### sk-perfect-overgroup
Does every f.g. amenable (or sofic) group embed in a f.g. PERFECT amenable (or sofic) group? This is gate G1 for embedding into simple Kazhdan linear-sofic or sofic envelopes (sk-sofic-embedding-a, e9d3f05c2b). Wreath products fail, because the abelianization is kept.

### sk-matricial-stability
Is SL_4(F_q[t^{±1}]) point-norm matricially stable? sk-cstar-mf (79f422ef29) shows G_X contains these lattices, and that the note's models are congruence representations on them. Stability would make C*_r(G_X) NOT MF, the analog of the SL_4(Z) node on main. The other answer is also informative.

### sk-rank3-lef-converse
Close rank 3 in `lef-el-groups-force-exactly-matricial-simple-ring`, which currently needs N ≥ 4. Then "EL_3(R) LEF ⟺ R exactly matricial" holds at the note's own rank.

### sk-trace-template
A trace-metric template theorem over products of gapped finite groups with bounded chief length (sk-fp-sofic-c, 4a4b6ad62c). It would reduce any finite-group hyperlinear model of an f.p. infinite simple group to alternating constituents.

### sk-strong-5 … sk-strong-8 (explorers)
Each explorer first lands a plan (at most 60 lines), then pursues it.
- sk-strong-5: a SECOND family of simple Kazhdan LEF groups with a strictly shorter complete proof of all properties than the note's (e.g. the lamplighter host over Z, or Toeplitz over Z²). If shorter, it could replace or accompany the headline.
- sk-strong-6: what the LEF iff theorem implies for approximation classes. For instance: which properties P (RF, MF, sofic, hyperlinear, weakly sofic) admit "P iff subgroup of a simple Kazhdan P group"? Prove the ones that follow and state the rest as sharp open problems.
- sk-strong-7: the single most impactful sentence about these groups that can be PROVED now, for operator algebraists (Connes embedding, QWEP, LLP, MF, Kirchberg's conjectures).
- sk-strong-8: free taste, aimed at findings that would change the note's headline.

## Family S: simpler

### sk-simpler-unify
After rev3 lands: unify §1 and §2 so there is ONE proof. State the theorem for a f.g. group acting minimally and topologically freely on a Cantor set (or subshift) whose crossed product has exact window models. Then Z-subshifts and the lamplighter host are examples. Measure the length honestly.

### sk-simpler-onepage
Integrate sk-open-2's one-page §1 v5 (PASS in sk-review-1) and sk-open-6's sequence formulation (PASS) into main's current text wherever they SHORTEN without loss. Deliver a candidate section plus a line count.

### sk-simpler-notation
A notation and readability pass on main's current tex:
- one symbol per object; no clashes (R the ring against 𝓡 the factor, n, k, w, N, x);
- consistent theorem, corollary and section structure;
- labels;
- display economy.

Deliverable: a §6 proposal.

## Family P: paper-level (these start from rev2, and switch to rev3 when it lands)

### sk-panel-referee-4 (dynamics), sk-panel-referee-5 (computability and group theory), sk-panel-referee-6 (expanders, (T) and approximation)
Hostile referees at the Annals, Inventiones or JEMS standard, each from their own area. Phase 1 reviews main's note as it stands, and the next revision when it lands, using the same method as sk-panel-referee-1..3 in ROSTER-D. Deliverables:
- blockers;
- what would make it astonishing;
- line-level fixes;
- credit gaps in their area.

### sk-intro-writer
The best possible introduction, at most one printed page:
- the question and its history;
- why it matters (Ozawa's LLP remark, Connes embedding context);
- the results in words (limit of finite simple expanders; LEF iff subgroup of a simple Kazhdan LEF group; the universal host; word problems);
- method and credit.

Build it from sk-lit-background's verified facts once they land. Deliverable: verbatim LaTeX with a changelog.

### sk-typesetting
Typographic and LaTeX polish of main's current tex: amsart conventions, theorem environments, \cite placement, bibliography style consistency, hyperref metadata, MSC codes, the MSI compile warnings (underfull boxes), and a pdf/A-style check of fonts. Deliverable: a proposal.

### sk-verify-6 (literature and credit)
Phase 1: independently spot-check the Kirchberg, Ozawa and Pestov quotations already on main, then serve `sk/queue/sk-verify-6.txt`. Verdicts go in `research/artifacts/sk-review-6-2026-09-13-partK.md`.

### sk-verify-7 (mathematics, wave 8)
Phase 1: review the density patch together with sk-strong-4's equivalence, since sk-verify-4 is overloaded. Coordinate by reading its queue and artifacts. Then serve `sk/queue/sk-verify-7.txt`. Verdicts go in `research/artifacts/sk-review-7-2026-09-13-partK.md`.
