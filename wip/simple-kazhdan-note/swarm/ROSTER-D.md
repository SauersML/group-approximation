# SK roster D: strongest results and an astonishing paper (wave 6, ~19:20)

The user, 19:15: "u have barely any agents" / "let's get agent swarm" / "on truly aking this an astonishly good paper" / "and strongest best possible results."
- Main drives the decisions; the log is `sk/drafts/rev2-decisions.md`.
- The base note on main is bf961c128b. Revision 1, from the editor lane, lands soon.
- Always read the note with `git show "${T}:simple_kazhdan_sofic_group.tex"` (T from sk/sktip.sh; braces are required in zsh).

Facts to build on:
- Reviewed PASS:
  - the constant-tower simplicity proof (F_2 and all q), with the covering step: translates of W cover X, so neither the simplicity of R nor Z(R) is needed;
  - LEF Replacement B;
  - the RF Toeplitz Theorem T and Corollary T (two PASSes each);
  - the local annihilation criterion;
  - S_∂ = EL_N(LC(∂F_d,F_q)⋊F_d)/Z is infinite, simple, Kazhdan and NONSOFIC.
- Unreviewed:
  - every f.g. RF group embeds in an infinite f.g. simple Kazhdan LEF group (sk-universal-embedding-a, 3bcc003284);
  - M_m(R_X) ≅ M_m(R_Y) forces strong orbit equivalence (sk-rigidity-ring, 2f116d20da);
  - a diagonal-preserving G_X ≅ G_Y exists iff X and Y are flip conjugate (sk-rigidity-intrinsic, e2430041ef);
  - the expanders and the explicit EJZ Kazhdan constant (20f65e6beb).
- WARNING: diag(a,a^{-1},1) is NOT a homomorphism on noncommuting units. Use diag(a,1,1) on derived subgroups.
- WARNING: over F_q the binary unit trick (LC(X,F_2)^× = {1}) fails; roots e_ij(e_C u) are needed.

Review requests: append one line to `sk/queue/sk-verify-4.txt` (embedding and structure families) or `sk/queue/sk-verify-5.txt` (rigidity, operator algebras, frontier).

## Family S: the strongest possible results

### sk-lef-embedding-e (the full-group route)
Target, shared with sk-lef-embedding-c/d and sk-universal-embedding-b: every f.g. LEF group embeds in an infinite f.g. simple Kazhdan LEF group.
- Start from this: [[T]]' of a minimal Z-subshift is LEF and not RF, and it embeds in G_X through diag(a,1,1). So some non-RF LEF groups already embed.
- Find which LEF groups embed in derived topological full groups of minimal ample groupoids whose Steinberg algebras are LEF and have local annihilation. Nonamenable examples need acting groups other than Z.
- Push to all f.g. LEF groups, or find the obstruction.

Peers: sk-universal-embedding-b, sk-lef-embedding-c, sk-lef-embedding-d.

### sk-sofic-embedding-a and sk-sofic-embedding-b
Target: every f.g. sofic group embeds in an infinite simple Kazhdan sofic group, so that sofic groups are exactly the f.g. subgroups of such groups. An obstruction also counts. Confirm the statement is open.
- Start (a): crossed products by sofic, non-LEF actions, and soficity of EL_n with Hamming-metric control. Respect the firewalls: linear, affine and projective targets force LEF (42196f9cb2), and Proposition F kills amenable actions.
- Start (b): ultraproduct envelopes, i.e. simple Kazhdan subgroups of metric ultraproducts of symmetric groups, built from rings acting on permutation modules.

Peers: each other.

### sk-hyperlinear-boundary-a and sk-hyperlinear-boundary-b (moonshot)
Is S_∂ hyperlinear? A yes gives the first hyperlinear nonsofic group, a famous open problem.
- First read the un-hyperlinear-paradox nodes and firewalls on main. HS transport fails at the Ad-Lipschitz step.
- Start (a): unitary models from the boundary action (quasi-regular representations, spectral approximation).
- Start (b): the von Neumann side. Either L(S_∂) ⊂ R^ω, or an obstruction such as Leavitt corner rigidity against tracial models.
- Be ruthless about hidden assumptions.

Peers: each other.

### sk-fp-sofic-c and sk-fp-sofic-d (moonshot)
Target: a finitely presented infinite simple Kazhdan group that is sofic or hyperlinear. This is Alekseev–Thom Open problem 6.1 in this form.
- sk-fp-sofic-a/b already landed firewalls (the gap theorem, isolation of SFT points, Proposition F). Pursue new ideas only.
- Start (c): tracial or metric approximations that are not permutations of algebraic sets, e.g. unitary models of EL_n over a finitely presented simple ring with a rank model.
- Start (d): group-theoretic candidates (Caprace–Rémy lattices, Titz Mite–Witzel, twin building lattices) and their local structure.

Peers: each other.

### sk-rigidity-f2
The one missing step toward "G_X ≅ G_Y implies strong orbit equivalence" over q = 2: every isomorphism EL_3(R_X) → EL_3(R_Y) is standard.
- Obstacles recorded by sk-rigidity-ring:
  - Petechuk: at n = 3 in characteristic 2, standardness fails in general;
  - R_X has no minimal idempotents;
  - there are nonunipotent elementary abelian 2-subgroups.
- Possible routes:
  - characterize root subgroups intrinsically, through the tower groups H_W ≅ GL_d(F_2);
  - the x³ = 1 idempotent trick;
  - centralizers of transvections.

Peer: sk-rigidity-cartan.

### sk-rigidity-cartan
Cartan uniqueness for R_X: is every maximal commutative, idempotent-spanned subalgebra whose normalizer generates R_X the image of LC(X) under a ring automorphism? Together with sk-rigidity-intrinsic's Theorem A, this would give "G_X ≅ G_Y iff flip conjugate". Peer: sk-rigidity-f2.

### sk-cstar-mf (bounded moonshot)
Is C*_r(G_X) MF? A yes would give the first infinite Kazhdan group with an MF reduced C*-algebra.
- Read the firewalls on main: norm-one outliers in the models, and no finite-dimensional unitary representations.
- Pursue only a new idea, for instance cuspidal or Steinberg-module models with no outliers, or strong convergence. Otherwise land a sharper firewall.

### sk-el2
Does EL_2(LC(X,F_2)⋊Z) have (T) and a simple quotient for every infinite minimal subshift, in particular Sturmian ones, where no Morita reduction exists?
- sk-hypotheses-sharp proved this when X has a finite cyclic factor (156ccae476).
- Routes: Ershov–Jaikin-Zapirain–Kassabov graded (T), or an obstruction.
- A yes means the note's theorem holds for n ≥ 2.

### sk-wp-embedding
Boone–Higman with (T) and LEF: a f.g. RF group has solvable word problem iff it embeds in an infinite f.g. simple Kazhdan LEF group with solvable word problem.
- Build on sk-universal-embedding-a's Toeplitz envelope.
- Control the computability of the subshift and of WP(Δ).
- The converse holds because subgroups inherit a solvable word problem.

### sk-strong-1 … sk-strong-4 (explorers)
Each explorer first lands `research/artifacts/sk-strong-<k>-plan-2026-09-13.md` (at most 60 lines), then pursues it.
- sk-strong-1: the single strongest theorem about these groups that can be proved this week and would change how people see simple Kazhdan groups.
- sk-strong-2: a different construction that gives more properties at once (prescribed finite subgroups, bounded generation, explicit presentations of the finite models, ...), with a proof as short as the note's.
- sk-strong-3: the most astonishing corollary for a non-specialist (operator algebras, computability, dynamics, expanders), proved.
- sk-strong-4: sharp boundaries. Exactly where the method stops (acting groups, coefficients, ranks, approximation types), stated as clean iff theorems.

## Family P: the paper itself

### sk-draft-minimal, sk-draft-rich, sk-draft-general, sk-draft-ring
Each drafter writes a COMPLETE candidate paper in `sk/drafts/<lane>/`.
- Compile on MSI: pdflatex, 3 passes, 0 errors, 0 overfull boxes, 0 undefined references.
- Use reviewed mathematics. Name any unreviewed item in your report.
- Follow the RULES §6 doctrine.
- Start from main's current tex and `sk/drafts/rev2-decisions.md`, and rebase onto revision 1 once it lands.

Architectures:
- sk-draft-minimal: the shortest astonishing answer: theorem, proof and at most one corollary, at most 3 pages.
- sk-draft-rich: theorem, the two strongest corollaries that pass review (candidates: RF embedding, operator algebras Option B, Turing degrees), and a questions paragraph of at most 15 lines.
- sk-draft-general: the headline over f.g. groups with free minimal subshifts that have finite models. Z is the main example, where no hypothesis is needed, and the RF embedding is an immediate corollary.
- sk-draft-ring: the headline for f.g. simple rings with local annihilation over any finite field and n ≥ 3, with subshift algebras as the example. Compare lengths honestly.

Deliverables:
- the tex path and the page count;
- a changelog against main;
- a one-page self-assessment: the strongest claim, the weakest point, what a referee will attack.

Land the self-assessment as `research/artifacts/<lane>-2026-09-13.md`; the .tex stays in drafts. Peers: the other drafters and sk-panel-referee-*.

### sk-panel-referee-1, sk-panel-referee-2, sk-panel-referee-3
Independent hostile referees at the Annals, Inventiones or JEMS standard.

Phase 1: read main's tex and all sk proposals and reviews. Write "what blocks acceptance at a top journal, and what would make this astonishing": missing strongest results, framing, correctness risks, credit risks, length.

Phase 2: review the candidate papers once `sk/drafts/<lane>/*.tex` exist, and each revision main lands.
- Check with a background Bash loop every 10 minutes, capped at 3 h.
- Rank the drafts and give line-level fixes.

Land `research/artifacts/sk-panel-referee-<k>-2026-09-13-partK.md`. Report an ERROR in anything on main to main at once.

Emphases:
- -1: group theory and correctness;
- -2: operator algebras, credit and lineage;
- -3: exposition, structure and impact.

### sk-title-abstract
Title, abstract, first paragraph and theorem statement: across all proposals and drafts, find the formulation a top-journal reader remembers.
- Keep the lineage Brown 2001 → Ozawa 2003 → Pestov 2008 accurate.
- Give three title-and-abstract variants with reasons, in a proposal.

### sk-reader
Simulate a strong graduate student reading main's tex line by line, then revision 1 and the drafts.
- Log every stall, every undefined symbol, every step that needs more than a minute with paper and pencil, and the one sentence that would fix it.
- Deliver a proposal.

## Family V: verification capacity

### sk-verify-4 (embedding and structure families)
- Phase 1: a second independent review of `rf-groups-embed-in-simple-kazhdan-lef-groups` and all its inputs (3bcc003284), and of sk-general-actions-a's three claims (e3d0976807).
- Phase 2: serve `sk/queue/sk-verify-4.txt` with the waiting rule of sk-referee-1.
- Verdicts go in `research/artifacts/sk-review-4-2026-09-13-partK.md`.

### sk-verify-5 (rigidity, operator algebras, frontier)
- Phase 1: review:
  - sk-rigidity-ring Theorem R and Corollary R1 (2f116d20da);
  - sk-rigidity-intrinsic Theorem A and Lemma C (e2430041ef);
  - sk-operator-algebras' new claim and repairs (b01d8ea1f5);
  - sk-hypotheses-sharp's claims (156ccae476);
  - sk-open-3's Fibonacci claim (af0a220f33);
  - the explicit Kazhdan constant nodes (20f65e6beb).
- Before starting an item, read the queue files and review artifacts of sk-verify-3 and sk-referee-2, so nothing is reviewed twice without reason.
- Phase 2: serve `sk/queue/sk-verify-5.txt`.
- Verdicts go in `research/artifacts/sk-review-5-2026-09-13-partK.md`.
