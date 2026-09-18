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
