# SK roster A: referees, credit, questions, generality, proofs

Each brief is a starting point, not a cage (RULES §1). Line numbers refer to `$SK/manuscript-disk-1646.tex`.

## sk-referee-1 (referee, then verifier for the general-theorem and proof lanes)
Phase 1: write an independent referee report on the note, at the standard of Inventiones.
- Check every sentence and index:
  - tower heights (is 2w+3 enough everywhere it is used?);
  - the commutator identity at l.210-214;
  - the subring argument at l.185-187;
  - why the corner of k is invertible and what "corresponds to a locally constant function κ" needs;
  - H_W ⊆ G;
  - the level-ideal step.
- Label each finding:
  - ERROR: a false claim;
  - GAP: a missing justification the reader needs;
  - UNCLEAR: a place where a competent reader stalls;
  - FREE STRENGTHENING: a stronger statement at the same length.
- Land `research/artifacts/sk-referee-1-report-2026-09-13.md`, with a §6 proposal for each fix. If you find an ERROR, SendMessage main at once.

Phase 2: verifier for `$SK/queue/sk-referee-1.txt`.
- Give each claim PASS, GAP (with a repair) or FAIL, in `research/artifacts/sk-review-1-2026-09-13-partK.md`.
- If a node's status must change, message the owner lane with the verdict.
- When the queue is empty, wait with a background Bash loop that exits when the queue file changes (check every 60 s, cap 3 h), then continue.

## sk-referee-2 (referee, then verifier for the consequence lanes)
Phase 1: write an independent referee report with a different emphasis.
- Finite models (l.118-152):
  - Are "the same words of length 2k+1" enough for every listed product, including shifted windows?
  - Is N larger than twice the largest exponent enough?
  - Are inverses handled?
  - Are the definition of LEF and the deduction of sofic and hyperlinear correct and correctly cited?
- The corollary (l.229-262):
  - the upper-bound algorithm, and the effective conversion to a group word;
  - the Sturmian facts: the language is computable from α, the minimum number of 1's is ⌊nα⌋, and the interleaving trick gives every degree;
  - the word-problem degree as an isomorphism invariant.
- Same labels and deliverables as sk-referee-1, in `sk-referee-2-report`.

Phase 2: verifier for `$SK/queue/sk-referee-2.txt`, in `sk-review-2-...`, with the same waiting rule.

## sk-citations (every citation and credit sentence, checked against its source)
Checks:
- EJZ Theorem 1.1, exact wording: associative, unital, finitely generated, n ≥ 3; EL_n or E_n; Kazhdan constant.
- What Grigorchuk–Medynets actually prove, and whether "the periodic-approximation mechanism of GM" credits them accurately (compare Vershik–Gordon, Matui).
- Is Nekrashevych 2016 the right reference for "the subshift algebra is classical"?
- Stepanov 1997, and what the "normal-structure tradition" sentence should cite (Bass 1964, Vaserstein, Golubchik).
- Thom 2010 Theorem 1.4, verbatim.
- Brown arXiv v1 §11 Question 7, verbatim.
- Ozawa, journal version p. 527, verbatim.
- Pestov BSL 2008: the question's numbering in each version, and what the journal prints.
- The exact BCFS, Clark–Edie-Michell and Steinberg results for simplicity and centre over F_2.
- The Sturmian facts: Morse–Hedlund, or a better source (Lothaire, Algebraic Combinatorics on Words, ch. 2).
- Every DOI via Crossref; journal, year, pages.

Deliverable: `sk-citations-proposal`, marking each bibitem and each credit sentence VERIFIED (with a quote) or FIX (with a replacement). Peer: sk-novelty.

## sk-novelty (prior art and exact novelty, with the bound of the search stated)
Search for:
- earlier infinite simple Kazhdan groups that are LEF, sofic or hyperlinear: Kac–Moody lattices, Ershov's golden groups, EL_n over simple rings, Kassabov–Nikolov, ultraproduct constructions, de Cornulier, Caprace–Rémy, Thom, Kionke–Schesler, "limits of finite groups with (T)";
- earlier EL_n over crossed products, Steinberg algebras or Leavitt algebras with (T) and simple quotients;
- earlier elementary-matrix extraction arguments;
- the ex-fp-simple-sofic landings on main.

Deliverable:
- a precise novelty statement for each theorem and corollary;
- the credit sentences the note must carry;
- any result in the note that is already known, with its source.

Peers: sk-citations, sk-questions-oa, sk-questions-ggt.

## sk-questions-oa (published open questions the group or a variant answers: operator algebras)
Mine these, with verbatim quotes:
- Brown, Mem. AMS 2006 (the expanded Question 7);
- the Brown–Ozawa 2008 book;
- the Capraro–Lupini book;
- Kirchberg 1993/1994 (the factorization property);
- Ozawa's surveys;
- Dadarlat (MF groups, quasi-representations);
- Carrión–Dadarlat–Eckhardt;
- Schafhauser;
- Thom;
- Peterson and Bekka (character rigidity);
- Popa, Ioana.

For each question, decide whether G_X answers it as stated or through a one-line variant, and write the sentence the note would carry. Deliverable: `sk-questions-oa-proposal`. Peers: sk-operator-algebras, sk-characters.

## sk-questions-ggt (the same for group theory and dynamics)
Mine:
- de Cornulier–Guyot–Pitsch (the space of marked groups, isolated groups, limits of finite groups);
- Grigorchuk;
- Arzhantseva–Păunescu;
- Glebsky–Rivera;
- Bradford (LEF growth);
- Becker–Lubotzky and Becker–Chapman (stability);
- Lubotzky–Oppenheim;
- Kun–Thom;
- Gelander;
- Caprace–Rémy;
- Juschenko–Monod, Matui, Grigorchuk–Medynets, Nekrashevych;
- Kionke–Schesler;
- Ershov;
- the Kourovka Notebook (search Kazhdan, LEF, sofic, simple).

Deliverable: `sk-questions-ggt-proposal`. Peers: sk-lef-growth, sk-expanders-limits, sk-universal-embedding-a.

## sk-general-master (the right generality, with the same short proof)
Extract the minimal ring-level hypotheses under which the note's three steps work:
- (T) needs finite generation.
- LEF needs a ring-level LEF property (injective partial models into finite rings). For countable simple R this is an embedding into an algebraic matrix ultraproduct over finite fields.
- Simplicity needs a simple R, a small centre, and "local matrix units": finite sets absorbed into corners isomorphic to M_d(LC(U,F)). Make this precise and compare `local-annihilation-makes-projective-el-simple`.

Find the most beautiful master theorem whose proof is no longer than the note's, then decide on reader merits whether the note should state it or the concrete theorem. Model-test the axiom on the Weyl algebra in characteristic p, Leavitt algebras, matrix rings, F_q[t], and LC(X)⋊Z². Peers: sk-proof-minimal-conceptual, sk-coefficients.

## sk-general-actions-a (beyond Z, with the note's proof)
For a f.g. group Γ acting minimally and freely on a subshift X ⊆ A^Γ: when is EL_n(LC(X,F_q) ⋊ Γ)/Z infinite, simple, Kazhdan and LEF?
- The tower lemma needs only freeness.
- LEF needs exact finite pattern models: finite Γ-sets realizing every F-pattern of X and no others, e.g. residually finite Toeplitz actions.

Start from `un-rf-beyond-free-2026-09-13-part{1,2}.md` and un-measure's Theorem A. Aim for the cleanest hypothesis in dynamical language, the shortest proof, and examples beyond Z (SL_3(Z), free groups, Z^d Toeplitz). Deliverable: a proposal for a remark or a generalized theorem, with its length cost. Peers: sk-general-actions-b, sk-universal-embedding-a.

## sk-general-actions-b (the same question, starting from the converse)
For free minimal Γ-subshifts, EL_n is LEF ⟺ the ring is LEF ⟺ exact pattern models exist (un-lef-converse, `lef-el-groups-force-exactly-matricial-simple-ring`).
- Which Γ admit such X, and which Γ force it (virtually free, class N)?
- For Z^d, which subshifts qualify?
- Is there a one-line sharp dichotomy the note should carry?

Deliverable: proposal. Peer: sk-general-actions-a.

## sk-stable-rank-a (a three-line simplicity proof through stable rank?)
- Determine the Bass stable rank of R = LC(X,F_q) ⋊ Z.
- Find and quote verbatim the sandwich theorem for GL_n or E_n over an arbitrary associative ring under a stable-range hypothesis: Bass 1964 Thm 4.2, Vaserstein 1969/1971, Hahn–O'Meara §4, Magurn. Record its exact range of n.
- If sr(R) is small enough for n = 3, simplicity of EL_3(R)/Z reduces to R being simple plus Z(R), and l.154-227 could shrink to a citation.

Starting points:
- the algebraic analog of Putnam's large subalgebra (functions times u supported off a clopen set Y, which is locally matricial over LC of towers);
- Laurent-polynomial arguments;
- whether R is an exchange ring, or has stable rank 1.

Deliverable: a proposal that compares lengths honestly, a Bass–Vaserstein citation against the self-contained tower proof. Peers: sk-stable-rank-b, sk-simplicity-short-a.

## sk-stable-rank-b (the same question, independent start)
Possible routes:
- Vaserstein's local stable range and quasi-finite rings;
- known stable-rank results for algebraic crossed products and Leavitt path algebras (Ara–Pardo);
- K_1-surjectivity;
- a counterexample with sr(R) ≥ 3, which would kill the shortcut at n = 3.

Deliverable: a proposal, or a firewall node. Peer: sk-stable-rank-a.

## sk-simplicity-short-a (the shortest self-contained simplicity proof)
Any approach is open:
- the normal closure of a single tower transvection;
- "G is generated by the finite simple groups H_W";
- directed unions of tower subgroups over refined partitions;
- the Stepanov–Vaserstein decomposition of unipotents;
- a better choice of h than e_ij(s).

Target: a complete proof that every nontrivial normal subgroup is G, shorter than l.154-227 and as rigorous. Put the candidate text in the proposal. Peers: sk-simplicity-short-b, sk-stable-rank-a.

## sk-simplicity-short-b (the same target, independent start)
Start from the ring side. Options:
- show directly that the normal closure of any nontrivial g contains e_12(e_W), by localizing inside M_3(B_m(U)) and conjugating, without the simplicity of GL_d(F_2) or using only perfectness;
- merge the extraction step and the level-ideal step into one lemma.

Keep whichever proof is shorter. Peer: sk-simplicity-short-a.

## sk-lef-short (the shortest, most useful LEF proof)
Options:
- R embeds in an algebraic ultraproduct ∏_ω M_N(F_2), so GL_3(R) embeds in ∏_ω GL_{3N}(F_2), and a countable subgroup of an algebraic ultraproduct of finite groups is LEF;
- return-word periodic points;
- orbit representations of periodic points.

Make the combinatorial lemma on periodic words as short as possible, and bound N explicitly by the recurrence function of X. Deliverable: a proposal replacing l.118-152. Peers: sk-lef-growth, sk-proof-minimal-concrete.

## sk-proof-minimal-concrete (the whole proof at minimum length, concrete)
Rewrite l.67-227 as a complete proof in concrete matrix language, as short as rigor allows. Keep every step a careful reader needs and cut the rest. Deliverable: the full candidate section in the proposal, with a line-count comparison. Peer: sk-proof-minimal-conceptual.

## sk-proof-minimal-conceptual (the same, conceptually)
Recast the proof as one or two lemmas about rings with local matrix units and LEF rings, from which the theorem follows in a few lines. Same deliverable, plus a reader-merits verdict on which version is better. Peers: sk-proof-minimal-concrete, sk-general-master.

## sk-coefficients (F_q, n ≥ 3, and the centre)
- For R_q = LC(X,F_q) ⋊ Z and n ≥ 3, compute Z(EL_n(R_q)) exactly: which scalars cI lie in EL_n?
- Check that the proof gives EL_n(R_q)/Z infinite, simple, Kazhdan and LEF for all q and n.
- Also look at coefficients in finite simple rings and in infinite fields, where finite generation or (T) may fail.
- Decide on reader merits: state F_2 with a remark on F_q, or state F_q.

Deliverable: proposal. Peer: sk-general-master.

## sk-expanders-limits (are the finite models expanders converging to G_X?)
Verify and sharpen:
- With d = |A|+2 ring generators, each finite model is a quotient of the universal lattice EL_3(F_2⟨x_1..x_d⟩) through a ring surjection onto M_N(F_2). Check that D_y(e_a) and P generate M_N(F_2) when y has least period N.
- EJZ gives a uniform Kazhdan constant. So the Cayley graphs of SL_{3N}(F_2) with the images of the generators are expanders, and they converge to G_X in the space of marked groups.
- So G_X is a marked limit of finite simple groups with a uniform Kazhdan constant.

Credit Kassabov (unbounded-rank expanders). Start from `pestov91-four-regular-expanders-and-limits-2026-09-13.md`. Decide whether the corollary is new, true, and worth two sentences. Deliverable: proposal. Peer: sk-questions-ggt.

## sk-rigidity-ring (what does G_X remember about X? via rings)
- Does G_X ≅ G_Y give an isomorphism or anti-isomorphism of the M_3 rings? Look at the isomorphism theorems for EL_n/GL_n over associative rings (Golubchik–Mikhalev, Zel'manov 1985, Bunina), and check characteristic 2 carefully: these theorems often need 1/2.
- K_0 with its order and unit (`subshift-crossed-product-k0-is-coinvariant-group`, Giordano–Putnam–Skau) then gives strong orbit equivalence.
- A ring isomorphism may give flip conjugacy, through algebraic Kumjian–Renault reconstruction for Steinberg algebras, diagonal-preserving or not.

Target: the sharpest true statement, e.g. "G_X ≅ G_Y iff X and Y are flip conjugate", or "G_X determines the ordered K^0 group". Start from `un-orbit-equivalence-2026-09-13-part{1,2}.md`. Deliverable: a proposal; this could replace the Turing corollary as the source of "continuum many". Peers: sk-rigidity-intrinsic, sk-word-problem.

## sk-rigidity-intrinsic (the same question, reconstructing X by group theory alone)
Recover the Boolean algebra of clopen sets, and the shift, from G_X using only group theory:
- the finite subgroups H_W ≅ GL_d(F_2) over towers;
- centralizers of transvections;
- the root subgroups e_ij(LC(U));
- maximal elementary abelian 2-subgroups;
- Rubin-type reconstruction.

Same target as sk-rigidity-ring. Deliverable: proposal. Peer: sk-rigidity-ring.
