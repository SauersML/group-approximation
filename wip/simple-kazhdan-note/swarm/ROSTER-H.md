# SK roster H: wave 10 (~21:45)

User, after I stated the goal: "nice. do u want more agents? u have barely any".
The goal: make `simple_kazhdan_sofic_group.tex` short, elegant and high-impact, with the strongest verified results and correct credit, and have everything on main and in Cairn.

## State (read on main with `T=$($SK/sktip.sh)` and `git show "${T}:<path>"`)
- **Note:** rev3 landed at 9047d0d3c9 (618 lines, 7 pp). Both rev3 referees found NO ERROR:
  - `research/artifacts/sk-rev3-referee-a-2026-09-13.md`
  - `research/artifacts/sk-rev3-referee-b-2026-09-13.md`
- **Rev4:** sk-editor-4 is assembling it into `$SK/drafts/rev4*.tex`. Plan: decision log item 71 in `wip/simple-kazhdan-note/decisions.md` (items 1–83).
  - (a) Theorem 2, the general engine (sk-simpler-unify, b64ae5d7fb);
  - (b) the shorter §1;
  - (c) headline: a f.g. group is LEF iff it is a subgroup of an infinite f.g. simple Kazhdan group that is a marked limit of finite simple SL_N(F_2) expanders (sk-strong-8 7e6f60b572, sk-strong-6 9d6965a225);
  - (d) the universal LEF host (sk-universal-lef-host-a/b) plus no decidable universal host (sk-wp-host 39a1b8550b);
  - (e) n ≥ 2;
  - (f) the new introduction;
  - (g) Questions;
  - optional: the SL_3(Z) obstruction (sk-sl3z-bandwidth 68539769be), character rigidity (sk-characters-rigidity-b d78467369d), the separable-factor result (sk-strong-7 fd87db53f7).
- **Reviews in progress (do NOT read their verdicts if you are a second reviewer of the same item):**
  - sk-verify-8: items (c), (d), characters, EL_2 over F_q, Theorem 2, rank-3 converse, wp-host, sl3z;
  - sk-verify-9: Theorem 2 and headline (c);
  - sk-verify-10: sk-strong-7;
  - sk-characters-rigidity-a: characters.
- **FALSE, never use:** diag(a,a^{-1},1) as a homomorphism; the "double swap" γ ↦ (γ,γ^{-1}); Kirchberg Cor 1.2 item (v) as printed (corrected by Thom).
- **Queues:** wave-10 research lanes queue claims in `$SK/queue/sk-verify-13.txt`, one line per claim: `<claim-id> | <lane> | <artifact path>`.
- **Rules:** `$SK/RULES.md` §2–§7 apply to every lane.
  - No .tex edits; landing only through skland.sh.
  - Land something within 30 min, then at least every 30 min.
  - Proposals quote the landed rev3 lines (md5 274f1936…), not the frozen disk copy.
  - Final report to main: at most 60 lines.

## sk-verify-11
Independent second review of item 71(d). Do not read sk-verify-8's verdicts on these items.
1. **sk-universal-lef-host-b** Theorem C (a303f6663a): one infinite f.g. simple Kazhdan LEF host contains every recursively presented f.g. LEF group; a countable set of f.g. groups lies in one host iff … (read the exact statement).
2. **sk-universal-lef-host-a:** A1 (the iff sentence) and A2 (drops the quotient-doubling overgroup via commutator words).
3. **sk-wp-host** (39a1b8550b): no decidable universal host.
   - Check hypothesis fidelity.
   - Model-test: the trivial group, a finite host, a host that is not simple.
   - Check where recursive presentation enters.

Verdicts: PASS / PASS-WITH-FIXES (verbatim) / FAIL (counterexample or missing step). Artifact `research/artifacts/sk-verify-11-2026-09-13[-partK].md`. Merge review lines onto claim nodes (skshow.sh, EX_ACK). Send a FAIL to main at once.

## sk-verify-12
Independent review of:
1. **sk-sl3z-bandwidth** (68539769be): GL_m(LC(X,F_q)⋊Z) has no distorted infinite-order elements, and the stable length is at least 1/(2wm) (a Krylov dimension count). Corollary: H_3(Z), SL_n(Z) for n ≥ 3, and BS(1,2) lie in no G_X, refuting `every-lef-group-embeds-in-a-z-subshift-elementary-group`.
   - Check the Krylov count for elements of support radius w.
   - Check the distortion facts: the Heisenberg centre is quadratically distorted; unipotents of SL_3(Z) are exponentially distorted (Lubotzky–Mozes–Raghunathan).
   - Check the credit to Cyr–Franks–Kra–Petite.
2. **sk-el2-fq** (fa92d5adcb): EL_2(LC(X,F_q)⋊Z) modulo centre is infinite, f.g., simple, Kazhdan and LEF for q > 2. The q = 2 case already PASSed.
   - Focus on the q-dependent steps: the roots e_ij(e_V u), the tower margin, SL_d quasisimple, the Peirce level step.
   - Check where (T) for rank 2 comes from.
3. **sk-rank3-lef-converse** (95cd5d55a7).

Same output rules as sk-verify-11.

## sk-verify-13
Serve `$SK/queue/sk-verify-13.txt` for wave-10 research claims. Poll it with a background loop, 60 s checks, up to 3 h.
First, in order:
1. **sk-measured-subshift** Theorem A, `sofic-lamplighter-bernoulli-crossed-products-have-rank-models`, and Theorem B, `sofic-groups-embed-in-simple-kazhdan-linear-sofic-groups` (db789b76bb, 38c836f9a6).
2. **sk-matricial-stability** (cc3d14e230): `laurent-sl-n-representations-have-sl2-invariant-vectors` and `laurent-sl4-stability-makes-overgroups-reduced-non-mf`.

Same output rules as sk-verify-11. Artifact `sk-verify-13-2026-09-13[-partK].md`.

## sk-answered-questions
Find every PRINTED question, problem or conjecture that the note's results answer or sharpen:
- simple Kazhdan LEF/sofic groups;
- LEF iff subgroup of a simple Kazhdan limit of finite simple expanders;
- the universal host and no decidable host;
- the SL_3(Z) obstruction;
- every Turing degree;
- continuum many R^ω-embeddable (T) factors, each separable factor holding countably many G_X.

Sources to check at source (fetch on MSI, quote verbatim with locators):
- the Kourovka Notebook (latest arXiv 1401.0300 version);
- Bekka–de la Harpe–Valette's open problems;
- Capraro–Lupini; Pestov's BSL survey; Thom's ICM 2018 paper; Ozawa's survey; Brown 2001 §11;
- Arzhantseva–Păunescu; de Cornulier–Guyot–Pitsch (space of marked groups); Grigorchuk 1984;
- Kassabov–Nikolov; Ershov–Jaikin-Zapirain; Juschenko–Monod; Kionke–Schesler; Alekseev–Thom;
- Belk–Bleak–Matucci–Zaremsky (Boone–Higman); Gelander's and Lubotzky's surveys;
- anything a web search turns up.

Deliverables:
- a table: question verbatim; source and locator; the answering result; fully or partially; the result's review status;
- a proposal naming at most 3 questions for the introduction, with verbatim LaTeX.

A "no printed question found" row must say how bounded the search was.

## sk-prior-art-2
Adversarial novelty check. For each claim below, search for prior publication (arXiv full text, zbMATH, web search, citations in the papers above) and grade it KNOWN (cite) / PARTIALLY KNOWN / NOT FOUND, stating the bounds of the search:
1. an infinite f.g. simple Kazhdan LEF group;
2. LEF iff subgroup of a f.g. simple LEF group (without (T)) — check Kionke–Schesler and earlier embedding theorems;
3. the same with (T);
4. f.g. simple Kazhdan groups that are marked limits of finite simple groups with expander Cayley graphs;
5. the universal LEF host;
6. no distorted elements in GL_m over subshift crossed products;
7. the separable-factor countability for G_X, against Nicoara–Popa–Sasyk 2007.

Deliverable: the grades plus verbatim corrections to any overclaim in rev3 or in the rev4 plan.

## sk-referee-significance
Hostile senior referee at the Annals/Inventiones/JAMS level. Read rev3 on main and decision log items 71, 79 and 83. Judge:
- significance, and the strongest HONEST framing;
- overclaims;
- what an expert expects and does not find (comparisons with Caprace–Rémy, Ershov–Jaikin-Zapirain, Kassabov–Nikolov, Thom, Juschenko–Monod, Grigorchuk–Medynets, Matui);
- the title, the abstract, the first paragraph;
- what to CUT, with line savings.

Deliverable: a ranked list, each item with verbatim proposed text and a one-sentence reader-merit reason.

## sk-iso-rigidity
Turn the note's rigidity question into a theorem.
- **Targets, in order of feasibility:**
  - (i) G_X ≅ G_Y ⇒ R_X ≅ R_Y or R_X ≅ R_Y^op. Tools: isomorphism theory of elementary groups over rings with many idempotents (Golubchik–Mikhalev, Zelmanov, Bunina, Hahn–O'Meara), or recovering root subgroups from commutation structure.
  - (ii) Recover [[T]]′ or LC(X,F_2) group-theoretically inside G_X. Then Bezuglyi–Medynets and GPS99 give flip conjugacy.
  - (iii) R_X ≅ R_Y ⇒ SOE or flip conjugacy.
- **Read first:** the artifacts of sk-rigidity-f2, sk-rigidity-cartan (99d9f9d236) and sk-cartan-counterexample (63e5151d57) on main.
- **Deliverable:** a theorem with a complete proof, or an honest obstruction map. Queue claims with sk-verify-13.

## sk-fp-sofic-host
Moonshot for the note's first question: an infinite finitely presented simple Kazhdan group that is sofic. Verify the exact printed status (Alekseev–Thom Open problem 6.1, verbatim; Caprace–Rémy lattices; soficity unknown?).
- **Read first:** the prior sk-fp-sofic-* artifacts on main (grep).
- **Fresh angles:**
  - finite presentability of St_n(R)/EL_n(R) for finitely presented simple rings R with sofic-type approximations;
  - Brin–Thompson/Nekrashevych-type rings;
  - rank-3 twin building lattices with sofic approximations from finite quotients of parabolics;
  - obstruction theorems (for example: f.p. + simple + some approximation property forces …).

A precise obstruction theorem is a valid deliverable. Queue claims with sk-verify-13.

## sk-sofic-host-hamming
The new Question for rev4: is every f.g. sofic group a subgroup of an infinite f.g. simple Kazhdan SOFIC group?
- **Build on:** sk-measured-subshift Theorem B (linear-sofic host), sk-sofic-embedding-a/b, and `amenable-groups-embed-in-simple-kazhdan-linear-sofic` (ef28dd4d20).
- **Attack:** the rank-to-Hamming barrier for these specific hosts:
  - permutation models of EL_3(LC(2^Δ,F_2)⋊L) built from actions on finite sets rather than on vector spaces;
  - sofic permanence (amalgams over amenable subgroups, Elek–Szabó, Hayes–Sale on wrinkled products);
  - even the amenable-input case (every amenable group inside a simple Kazhdan sofic group) is worth a theorem.
- **Deliverable:** a theorem, or an obstruction proving that these hosts need new ideas. Queue claims with sk-verify-13.

## sk-decidable-host
A Boone–Higman–Kazhdan theorem: a f.g. group is LEF with solvable word problem iff it is a subgroup of an infinite f.g. simple Kazhdan LEF group with solvable word problem.
- The easy direction is standard: WP passes to f.g. subgroups, and LEF passes to subgroups.
- **Hard direction:** make the host effective.
  - Computable LEF approximations exist, by search using the WP.
  - Build an effective Ore-type overgroup Δ with solvable WP.
  - Show that the lamplighter host ring over Δ has decidable zero-test, and the WP transfers to EL_3.
- **Check against:** sk-wp-host (no decidable UNIVERSAL host) and sk-wp-embedding; there must be no contradiction.
- **Deliverable:** theorem plus proof, or an obstruction. Queue claims with sk-verify-13.

## sk-lef-proof-compress
The shortest complete proof of Corollary 2 (LEF iff subgroup of an infinite f.g. simple Kazhdan LEF group), given Theorem 2 (sk-simpler-unify). Rev3 §2 is about 80 lines: Ore overgroup via doubled regular actions in ultraproducts of symmetric groups, lamplighter host, affine models, Whitehead identities.
- **Target:** at most 35 lines, with the same rigor.
- **Ideas:** commutator words instead of Ore (sk-universal-lef-host-a A2); marked-limit language instead of ultraproducts; a direct embedding of Γ into [L,L].
- **Deliverable:** verbatim LaTeX, compiled on MSI, and a proposal artifact with a line count. Queue with sk-verify-13.

## sk-two-generators
Is G_X generated by 2 (or 3) explicit elements, with the finite models SL_{3N}(F_2) and expansion on the images of those generators? A crisp statement ("a 2-generated infinite simple Kazhdan group …") costs one clause.
- **Literature:** generation of SL_n(Z) and EL_n over f.g. rings by few elements (Trott, Conder, Kassabov–Nikolov); two-generation of finite simple groups.
- **Deliverable:** theorem plus a short proof, or an honest status. Queue with sk-verify-13.

## sk-general-statement
Prepare the exact rev4 text for the most general verified form of Theorem 1:
- every finite field F_q;
- every n ≥ 2 (quotient by the centre where needed);
- finite models PSL/SL_{nN}(F_q).

Follow decision 74, R3: at most 12 proof lines naming the changes.
- Read sk-verify-12's landed verdicts when they exist; do not message it.
- **Deliverable:** verbatim LaTeX (statement plus delta), compiled on MSI, with a proposal artifact and a one-sentence trade-off.

## sk-questions-section
Rewrite §4 Questions into the best 3–5 open problems for the reader.
- Check that each is still open (bounded search) and give its precise printed source:
  - f.p. sofic simple Kazhdan (Alekseev–Thom 6.1, Caprace–Rémy);
  - the sofic host question;
  - isomorphism rigidity (GPS99/Bezuglyi–Medynets analogue);
  - C*-simplicity or MF of C*_r(G_X);
  - von Neumann rigidity.
- **Deliverable:** verbatim LaTeX (at most 20 lines) plus a status table in a proposal artifact.

## sk-cstar-simple-2
A second, independent angle on C*-simplicity of G_X. Read sk-cstar-simple's landed artifacts on main and do NOT duplicate its approach.
- **Angles:**
  - unique trace from Breuillard–Kalantar–Kennedy–Ozawa (trivial amenable radical);
  - Kalantar–Kennedy free boundary actions;
  - Le Boudec–Matte Bon micro-supported actions (is there a faithful micro-supported action of G_X?);
  - Kennedy's criterion (no nontrivial amenable uniformly recurrent subgroups) applied to the root and tower subgroups.
- **Deliverable:** a theorem with proof, or a precise obstruction. Queue with sk-verify-13.

## Later (launched by main when `$SK/drafts/rev4.tex` is ready)
sk-rev4-referee-a (correctness), sk-rev4-referee-b (credit, exposition), sk-rev4-referee-c (length and elegance: every sentence earns its place).
