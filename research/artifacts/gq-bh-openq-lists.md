# Open questions near Boone–Higman in problem lists (lane bh-openq-lists)

Lane `bh-openq-lists`, BH swarm, 2026-09-18. It is a companion to the paper-based list
`research/artifacts/gq-bh-openq-papers-list.md` (lane bh-openq-papers). This file covers
**problem lists**: AIM problem lists, Oberwolfach reports, workshop problem sessions,
the Baumslag–Myasnikov–Shpilrain list, and MathOverflow. The Kourovka Notebook belongs
to lane bh-kourovka and is not repeated here.

Sources were fetched on 2026-09-18 through MSI and read as text or PDF page images.
Wording is quoted from the source. "Main" means origin/main at the time of landing.

## A. Nodes landed with this artifact

| # | Question (source) | Node | Status | Tractability |
|---|---|---|---|---|
| A1 | Zaremsky, OWR Report 26/2018, p. 1624, **Question 110**: "Does the Higman group ⟨a,b,c,d \| b^a=b², c^b=c², d^c=d², a^d=a²⟩ embed into the Lodha–Moore groups? Or at least into Monod's H(**R**)?" | `higman-group-embeds-in-no-lodha-moore-or-monod-group` | ESTABLISHED (corollary; lane proof, not reviewed). **Answer: no** | settled by a node already on main |
| A2 | AimPL *Groups of dynamical origin*, Problem 3.1(c): "Is there a finitely presented simple group with commutator width greater or equal to 2?" | `fp-simple-group-with-commutator-width-at-least-two` | ANSWERED in the literature: Caprace--Fujiwara, arXiv:0809.0470, Cor. 1.4 (Kac--Moody groups over finite fields; infinite commutator width; also Kourovka 14.13). Corrected 09-18 by bh-free-19 | — |
| A3 | MathOverflow 491978 (A. Minasyan, 2025; update 08 July 2026): does B. H. Neumann's 2-generated group G ≤ ∏ A_{2n+1}, which contains ⊕ A_{2n+1}, embed in a finitely presented residually finite group? | `neumann-alternating-product-group-embeds-in-fp-rf-group` | OPEN | medium |
| A4 | MathOverflow 412219 (2021): "If G is finitely presented, does this imply that E(G) is recursively presented?", with E(G) = ⟨constant maps, id⟩ ≤ G^G | `e-of-finitely-presented-group-is-recursively-presented` | OPEN, with a lane-proved reformulation E(G) ≅ (G∗Z)/J_1(G) | medium–high |

**Why A1 matters.** Higman's group H4 is test case #1 of `bh-testcases` (54c5d8424).
Zaremsky proposed the Lodha–Moore groups because both they and H4 are built from BS(1,2).
Main already proves (09-13, `higman-group-embeds-in-no-piecewise-analytic-circle-group`)
that every homomorphism from H4 to a group of piecewise real-analytic circle homeomorphisms
is trivial. Monod's H(**R**) and the Lodha–Moore groups sit inside that class. So the
printed question has a negative answer from existing repo content, and nobody had noted
the connection. Priority: a bounded arXiv abstract search (2026-09-18) found no statement
about H4 in piecewise projective groups. Rivas–Triestino (arXiv:1905.00938) cover only C¹
actions. No MathSciNet search was made.

## B. Already on main: provenance only (two sibling nodes gain a second printed source)

| Question (source) | Existing node | Note |
|---|---|---|
| AimPL *Amenability of discrete groups*, Problem 5.2: "Is there a finitely presented simple group that is not 2-generated?" | `fp-infinite-simple-group-not-two-generated` | same question as Lodha's printed one; an "also printed" line is appended |
| AimPL *Amenability of discrete groups*, Problem 2.5: "Find an example of a Z²-action on a Cantor set such that the commutator subgroup of the topological full group is f.p." | `free-minimal-zn-derived-full-groups-are-never-fp` | Matui's question is for free minimal Z^N; the AimPL version allows any Z² action. An "also printed" line is appended |

## C. Recorded, no node (lower BH relevance, compute-heavy, or answered)

**AimPL *Groups of dynamical origin*** (http://aimpl.org/groupdynamorigin, accessed 2026-09-18):
- **Problem 2.2 (Nekrashevych).** "Is it true that for all finitely generated subgroup H ≤ F(Ω), H is either elementary amenable or for any K finitely presented subgroup such that K ↠ H, K contains a free subgroup?" This is about fp covers of full-group subgroups. It is adjacent to the fp-host questions, but not an embedding question.
- **Problem 3.1(a,b).** Boundedness and exact values of commutator width and involution width for F, T, V and topological full groups.
- **Problem 4.2.** When is the Nekrashevych C*-algebra of a contracting group simple?

**AimPL *Amenability of discrete groups*** (http://aimpl.org/amenablediscrete):
- **Problem 4.15.** "Is there a f.p. amenable infinite simple group?" The list suggests the derived subgroup of the Penrose tiling full group as a candidate. Famous and open. Main has neighbours (`fg-infinite-simple-groups-are-not-elementary-amenable`, `amenable-infinite-simple-circle-groups-fix-a-point`) but no node for the question itself. Low tractability.
- **Problems 4.7 / 4.65.** "Is there a 2-generated infinite simple amenable group?" Candidates are the Juschenko–Monod groups. Main now has one inside 2V (`smart-trace-full-group-embeds-in-brin-thompson-2v`, bh-amenable), but its rank is not recorded.
- **Problem 3.8** (a fp amenable group surjecting onto a group of intermediate growth) and **Problem 4.1**: amenability questions, not BH.

**AimPL *Geometry and topology of Artin groups*** (http://aimpl.org/geomartingp):
- Problems 2.1–2.4 (the word problem for all Artin groups) set the scope of BH inputs. Problem 6.1 (which Artin groups embed in mapping class groups) is a possible route for bh-artin. Problem 5.4 (solvable WP from NPC complexes with decidable cell stabilizers) is a permanence-type question. None is a node.

**AimPL *Rigidity properties of free-by-cyclic groups***: Problem 7.3 (S. Hughes), "Are free-by-cyclic groups linear?" BH for free-by-cyclic groups is settled on main (BLIW), so this is not BH-relevant.

**Oberwolfach Report 26/2018** (*Cohomological and Metric Properties of Groups of Homeomorphisms of R*, "Open problems on Thompson-like groups", pp. 1622–1625): Questions 100–113.
- Besides Q110 (A1), the relevant ones are **Q113 (Zaremsky)**, "In the family of Thompson-like groups, can one find non-finitely presentable groups of type FP₂?", and **Q112**, whether the kernel of the Lodha–Moore dot map is F∞.
- Q103, "Is V_br acyclic? What about the Brin–Thompson groups nV?", is homological.
- The report cites the St Andrews 2014 "extended family of R. Thompson groups" problem list (its [113]). That list was not obtained.

**AIM, *Thompson's group at 40 years*, preliminary problem list (January 2004)**, https://aimath.org/WWN/thompsonsgroup/thompsonsgroup.pdf.
- It is mostly about F: amenability, subgroups, geometry.
- The BH-adjacent items are Q4.7 (Guba, "What are the simple subgroups of F?") and Q5.2 (Brin, universality of the F construction for embedding infinitary structures).
- Neither has a crisp BH form, and many items have been answered since 2004.

**Bestvina, *Questions in Geometric Group Theory*** (updated July 2004): hyperbolic and CAT(0) structure questions. None asks for embeddings into fp simple groups. Not used.

**Baumslag–Myasnikov–Shpilrain list** (NYGTC, archived at web.archive.org, zebra.sci.ccny.cuny.edu/web/grouptheory.org/nygtc/problems/):
- **(FP9) (Baumslag, Cannonito, Miller).** "Is every countable locally linear group embeddable in a finitely presented group?" For recursively presented inputs this is Higman, and GL_n(Q) is settled on main (`gl-n-q-explicit-natural-fp-overgroup`). The general question is about non-recursive inputs. Not BH.
- **(FP17) (Remeslennikov)**, centres of fp groups; (A3), (O11): recorded only.

**MathOverflow** (StackExchange API, 2026-09-18):
- **324409** (Nyberg-Brodda, 2019, unanswered): is F₅ ∗_{F₂₅} F₅ (Caprace–Radu) the smallest simple Burger–Mozes-type amalgam? This is a fp-simple-group question, but it needs large computation. No node.
- **339541** (2019, unanswered): the d = 0 member of a Higman–Thompson-type family of topological full groups. Its derived subgroup is f.g. and simple; finite presentation is open. A possible target for bh-groupoid (Li's F∞ theorem). No node.
- **221091** (2015): does Higman's group have property (T)? It does not. H4 acts without a global fixed point on the Bass–Serre tree of its amalgam splitting (main: `higman-group-splits-as-amalgams-over-free-subgroups`), so it fails (FA) and hence (T). Answered.
- **489460** (Mikaelian, 2025): explicit Higman embeddings. The list consists of Kourovka 14.10(a) (answered by BHM and Mikaelian) and his own algorithm, arXiv:2507.04347. No new open item.
- **485085** (2024): how hard is classifying fp or fg simple groups? A meta question; no node.
- **73568** (2011): the BH conjecture itself (answered with references).

## D. Not obtained

- **AimPL index:** aimpl.org's TLS certificate had expired. Pages were fetched with certificate checks off (curl -k) on MSI.
- **St Andrews 2014 Thompson-family problem list:** not located.
- **Oberwolfach:** reports were searched through publications.mfo.de. Only 26/2018 had a Thompson-family problem session among the hits; other reports were not searched exhaustively.
- **Other lists:** the GAGTA and Groups St Andrews problem sessions, Kapovich's list and Bridson's list were not found online in a form reachable from MSI.

## E. Second pass (09-18, after the coordinator's follow-up)

**Correction.** A2 (AimPL 3.1(c)) was answered in the literature before the AIM list:
Caprace–Fujiwara, arXiv:0809.0470, Cor. `cor:KM:simple`, which also answers Kourovka
14.13. bh-free-19 corrected the node and the table at 6aa871f6e and 412254bb1; this lane
confirmed it from the TeX (l.262–295). The lesson for this lane: check the literature
before landing an OPEN node for a printed question.

**Lists reached in this pass.**
- **St Andrews 2014 Thompson-family list.** OWR 26/2018 [113] identifies it: Y. Lodha,
  *Broad themes and open problems surrounding Thompson's groups*, collected at the
  "Workshop on the extended family of R. Thompson groups" (organized by Bleak, Burillo and
  Sergiescu), St Andrews, 2014. The text itself was not found. It is not on the
  St Andrews CIRCA pages archived at web.archive.org, and web search from MSI returned
  nothing.
- **M. Sapir, *Some group theory problems*** (IJAC 17 (2007) 1189–1214; arXiv:0704.2899,
  TeX read on MSI; OWR [116]). Problem 1 asks to "find finitely presented monsters of
  types (1)–(7) or prove that they do not exist". Types (2), (3) and (4) are the Burnside
  and Tarski monsters, the setting of BBMZ 5.3(6) (`free-burnside-groups-satisfy-boone-higman`).
  The other problems (asymptotic cones, diagram groups, amenability of F, percolation) have
  no Boone–Higman content. No node.
- **Bridson–Vogtmann, *Automorphism groups of free groups, surface groups and free
  abelian groups*** (Farb's *Problems on mapping class groups*; arXiv:math/0507612, TeX
  read). Question 20 asks: "For which values of m does Out(F_n) embed in Out(F_m)?" Two
  further pointers: an embedding of a finite-index subgroup of `Out(F_n)` into some
  `Aut(F_m)` would give BH for `Out(F_n)`, by BFFHZ Theorem A and finite-index closure of
  B_A; and Bogopolski–Puga's embeddings `Out(F_n) ↪ Out(F_m)`, recalled not re-read, go
  through characteristic subgroups. Question 15 asks whether `Out(F_3)` is linear. These
  are pointers for bh-outfn (`out-free-groups-virtually-embed-in-aut-free-groups`).
- **AIM 2010, *The geometry of Out(F_n)*** (ed. Mangahas;
  https://aimath.org/WWN/outerauto/outerauto.pdf, read). Problem 4.1 asks, for closed
  `S`: "what is Hom(MCG(S), Out(F_n))? What about injective homomorphisms?" A virtual
  embedding of closed `Mod(S_g)` into some `Aut(F_m)` would give BH for BBMZ 5.3(2), the
  closed case. This is a pointer for bh-mcg. Problems 3.1–3.6 (property (T), largeness)
  have no BH content.
- **Farb, *Some problems on mapping class groups and moduli space*** (arXiv:math/0606432,
  TeX read). There are no embedding questions into simple or finitely presented groups.
  - Problem 15 asks for a sub-quadratic word problem algorithm for `Mod_g`.
  - Problem 65 asks whether some finite-index subgroup of `Mod_g` acts faithfully on
    `S^1`. A yes would be relevant to Thompson-type hosts, since T acts on the circle.
- **Kapovich-area list: AimPL *Boundaries of groups*** (http://aimpl.org/groupbdy,
  5 sections, read). It asks about Morse and CAT(0) boundaries, with no BH content. No
  personal problem list of Kapovich was found online.
- **Bridson's own list** (*Problems concerning hyperbolic polyhedra and non-positively
  curved complexes*): not found online. The Bridson questions in OWR and AIM lists are
  covered above.
- **GAGTA and Groups St Andrews problem sessions:** no published problem-session lists
  were found. The Groups St Andrews proceedings volumes are not freely online.

**Solving pass.** The most tractable question found is MathOverflow 412219 (the E(G)
question). The finitely generated version is now answered negatively:
`fg-decidable-group-whose-e-is-not-recursively-presented` builds a 3-generator group Γ,
recursively presented with solvable word problem, whose `J_1(Γ)` is not r.e. So `E(Γ)` is
not recursively presented, and it embeds in no finitely presented group. The finitely
presented case stays OPEN; the exact gap is Attempt 2 on
`e-of-finitely-presented-group-is-recursively-presented`.

## F. Third pass: printed questions in 2024–2026 arXiv papers (09-18)

**Method.**
- The arXiv API (math.GR) was queried for Thompson, topological full group,
  self-similar, Houghton, "finitely presented simple", Boone–Higman, Nekrashevych and
  Brin–Thompson. That gave 158 papers from 2024–2026.
- Papers already read by bh-openq-papers were dropped. TeX for the remaining 58 was
  fetched on MSI (`gqsrc/bh-openq/hunt2/`).
- Question, problem and conjecture environments were extracted, together with sentences
  containing "open", "we do not know", "natural to ask" and similar.

| # | Question (source, TeX line) | Node | Status |
|---|---|---|---|
| F1 | Tarocchi arXiv:2310.14660v3 l.1605 (also thesis 2412.02339 l.5583): "Is $[G_3, G_3]$ simple?" | `dendrite-rearrangement-group-g3-has-simple-commutator-subgroup` | **ANSWERED yes** (lane proof, this pass) |
| F2 | Tarocchi 2310.14660v3 l.1081–1085: dendrite rearrangement groups "Are they finitely presented? Are they $F_\infty$?" | `dendrite-rearrangement-groups-are-finitely-presented` | ANSWERED in the literature: Perego–Tarocchi arXiv:2412.04138v1 prove every $G_n$ is $F_\infty$ (bh-dendrite, 09-18) |
| F3 | Hill–Kwak–Udall–West arXiv:2508.21264 l.297: "whether the Boone--Higman conjecture for the graph Houghton group is true … whether the Boone--Higman conjecture holds for all Houghton-type groups" | `graph-houghton-groups-satisfy-boone-higman` | OPEN. The preprints review had screened this paper as low relevance, missing the BH question |
| F4 | Bodart–D'Angeli–Perego–Rodaro arXiv:2608.02111 sec7 l.134: "Does any (weakly) branch group embed in Thompson's $V$?" | `finitely-generated-weakly-branch-group-embeds-in-thompson-v` | OPEN for f.g. groups. The literal reading is answered yes by the finitary automorphism group (lane remark on the node) |
| F5 | Kodama arXiv:2602.04839 l.869: "it is not known whether $G_0(n)$ is a subgroup of $\PPSL$ or not" | `n-adic-lodha-moore-groups-embed-in-piecewise-projective-group` | OPEN. It bears on the Higman-group obstruction |
| F6 | Garrido–Reid arXiv:2501.00908 l.3035: "Let $G$ be a minimal piecewise full group of homeomorphisms of the Cantor space. Is $\Der(G)$ simple?" | `minimal-piecewise-full-group-derived-subgroup-is-simple` | OPEN |

**Recorded, no node.**
- **Hill–Kwak–Udall–West 2508.21264, l.299:** "in the two ended case is there a
  finitely presented dense subgroup?" of mapping class groups of graphs and surfaces.
- **Bodart–D'Angeli–Perego–Rodaro 2608.02111:** whether all Schreier graphs of a f.g.
  branch group have finitely many ends (l.151), which would give a negative F4. Also
  solvable subgroups of V and polynomial-growth graphs (l.134, l.191, l.194). Lehnert's
  conjecture is already on main.
- **Perego–Tarocchi 2412.04138, l.2699:** "Is $E_{\mathcal{D}_3}\mathbb{G}$ finitely
  presented? Is it $F_\infty$?" (eventually self-similar groups).
- **Tarocchi thesis 2412.02339, l.5312 and l.5863:** density and conjugacy questions.
- **Garrido–Reid 2501.00908:** the remaining questions are about t.d.l.c.
  compact generation, branch groups and local isomorphism classes.
- **Surface groups in V:** restated in 2608.16530 l.143, citing Bleak–Matucci–Neunhöffer Question 7. Already on
  main as `closed-hyperbolic-surface-groups-embed-in-thompson-v`.
- **Other 2024–2026 questions** with no Boone–Higman content:
  - the maximal-subgroup problem for the Higman–Thompson groups F_n (2607.04038, Problem `prob:minimal-maximal`);
  - co-Hopficity of pure surface Houghton groups (2403.04941);
  - (2,3)-generation of V_n (2411.09069);
  - pseudocentre questions (2511.21175);
  - Stein-group problems (2412.05492);
  - mixed identities of oligomorphic groups (2606.24741, Conjecture 1 of
    Bodirsky et al., which that paper settles in part);
  - CSS* groups (2507.18821);
  - spread of vigorous groups (2607.21754);
  - asymptotically conformal MCG (2609.08849).

**Solving pass.** F1 was the most tractable, and it is now answered.
- Tarocchi's own reduction leaves `G'/N` cyclic, generated by the image of the
  3-cycle `c = τ_2τ_3`.
- Conjugating by `g = τ_2 ρ_12 ∈ G'` gives `g c g^{-1} = c^{-1} Y`. The error term
  `Y = ρ_22 ρ_12` is a commutator of two elements of one rigid stabilizer, namely
  `[τ_2 σ, ρ_12 σ]` with `σ = ρ_312`.
- So `c ≡ c^{-1}` modulo `N`, and `c ∈ N`.

**Posted for bh-free-08** (owner of the finitely presented case of MO 412219): the
E(G) insights are on its board.

## G. Fourth pass: structural questions in 2025–2026 papers and problem lists (09-18, INSIGHT FIRST)

**Method.**
- The arXiv API was queried over 24 more math.GR topics (489 papers from 2025–26),
  and papers already read were dropped (402 left).
- 40 were chosen for Boone–Higman structure (closure, universal hosts,
  characterizations). Their TeX was read on MSI (`gqsrc/bh-openq/hunt4/`).

| # | Question (source) | Node | Status |
|---|---|---|---|
| G1 | Bishop–Schesler arXiv:2509.12161v2, Theorem B and Corollary `cor:boone-higman`: BH for EFRF^+ groups reduces to EFRF^+ branch groups | `efrf-groups-frattini-embed-in-efrf-branch-groups` | ESTABLISHED (literature import) |
| G2 | Bishop–Schesler l.212: "Does every finitely generated residually finite group $G$ with solvable word problem embed in a finitely generated branch group with solvable word problem?" | `rf-decidable-groups-embed-in-decidable-fg-branch-groups` | OPEN. Settled for EFRF^+ inputs; equivalent to its non-effective (Rauzy) case |

**The structural point of G1.** All fp RF groups are EFRF^+. So BBMZ 5.3(2) closed MCG,
5.3(3) Out(F_n), 5.3(7) fp metabelian and 5.3(12) fp RF all reduce to Boone–Higman for
one class: finitely generated, recursively presented, EFRF^+ spinal branch groups over
computable growing alphabets. Unlike main's self-similar route, this route has no
regular-tree failure point.

**Recorded, no node.**
- **Darbinyan–Steenbock arXiv:2504.12707, Question `quest-1`:** "Does there exist a
  countable group with no computable left-order that embeds into a finitely-generated
  group with computable left-order?" Lane remark: on the literal reading the answer is
  yes.
  - Take `Q_S = <1/p : p ∈ S>` for a non-c.e. set of primes `S`. A computable copy
    would make `S` c.e. up to finite difference, so `Q_S` has no computable copy and
    hence no computable left order.
  - `Q_S ≤ Q`, and `Q` computably embeds in a finitely generated group with computable
    left order, by their Theorem `thm-finitization`.
  - The intended reading presumably requires `G` to be computable with no computable
    copy carrying a computable left order (Harrison-Trainor). That reading stays open.
- **Darbinyan–Steenbock Question 2:** "Is there a quasi-isometric version of
  Boone-Higman's theorem for left-orderable groups?"
  - Their family theorem (`T: family computable left order`) plus Olshanskii's
    undistorted Higman embedding already give a version: a finitely generated group
    has a computable left order iff it QI-embeds in a finitely generated simple group
    with computable left order that is QI-embedded in a finitely presented group.
  - The converse direction is their Lemma 2.2 of arman_new.
  - The real open core is a left-orderable Thompson theorem: every finitely generated
    left-orderable group with decidable word problem into a finitely generated simple
    left-orderable group with decidable word problem.
- **Fournier-Facio–Zaremsky arXiv:2607.21727 (Higman's rope trick):** Questions
  `quest:higher_F` and `quest:higher_FP` (embedding in F_n and FP_n groups), and
  Theorem A (recursively presented FP_n hosts give F_n hosts). Already used on main
  (`acyclic-host-*` nodes; BBMZ Q5.6 node).
- **Hyde–Lodha arXiv:2509.09788:** finitely generated highly transitive MIF
  overgroups that preserve amenability or no-free-subgroups. It bears on the BFFHZ
  route, which needs MIF hosts. No printed open question beyond the one it answers.
- **Problem list on foliations and diffeomorphism groups, arXiv:2503.18274** (a
  conference problem list, l.328–340):
  - "For any $n\geq 2$, is there a simple orderable group of type $F_n$ but not
    $F_{n+1}$?"
  - "Is there a finitely presented, or even type $F_\infty$, boundedly acyclic simple
    orderable group?"
  - "Are Burger--Mozes' examples of simple groups orderable?"
  - Epstein's "Is $PL_0(M)$ … a simple group?" (l.1142).
  - These concern orderable fp simple groups, which are left-orderable-host questions
    for Boone–Higman.
- **Problems on handlebody groups, arXiv:2502.21177:** no Boone–Higman question.
  Handlebody groups sit inside closed-surface MCGs, so they inherit any answer to
  BBMZ 5.3(2).
- **Rauzy arXiv:2002.02540** (read for G2): Dyson groups `L(A)`. They are RF iff `A`
  is profinitely closed, and EFRF iff `A` is effectively closed.

**Lesson for general BH (this pass).** The residually finite part of the open list is
a single host problem. Build finitely presented simple overgroups for spinal branch
groups over computable growing alphabets, the Bishop–Schesler groups. The
non-effective residually finite inputs of Rauzy are harmless for Boone–Higman, since
simple hosts are never residually finite. So effectiveness matters only for
intermediate residually finite hosts.
