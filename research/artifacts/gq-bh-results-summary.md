# Boone–Higman swarm: printed problems answered on 2026-09-18, the mechanisms, and the corrections

Lane `bh-writeup`, written from node texts on origin/main at `ddeea47ea` (14:25 CDT). Updated at
`40650f1e7` (16:05 CDT) with these referee passes:
- `fac0259d6`: 21.74(b),(c) and 21.75;
- `6a0a3642f`: MO 339541, Kohl's factorization and the RSV doubles;
- `5821ec240`: 17.60 and 21.73.

The update also covers the LISW Q1.11 row, the Matui reduction (`f2350f8a4`) and the new general
mechanisms (§7a).

Updated again at `e8df48ee6` (16:21 CDT):
- the credits section (§0);
- FFWZ Q5.9 (`25056ab91`);
- the wider Tanner result (`fd9f710c0`);
- Reid's group not finitely presented (`5d7507af3`, `bb487abce`, `58db3f3f9`);
- Kourovka 21.74(a) (`d61d20b6b`) and 17.58 (`ad962750f`), both still open.

Updated again at `5a7d8353e` (16:43 CDT):
- referee passes for 17.61 and BFFHZ Q3.1 (`4697bc8f5`), FFWZ Q5.9 (`9dfa9e546`) and Reid's non-fp
  (`a23f54860`);
- T_{2,3}, T_τ, V_τ finitely presented (`8c548b3da`, §5);
- the Kourovka 21.140 reduction (`6dc3f9d10`, §4).

Updated again at `21a63f269` (16:53 CDT):
- The BS(1,2) chain claims failed review (`4b2fdd3d9`) and are OPEN (§8). This summary never
  listed them as results.
- These remain referee PASS: Kourovka 21.74(b,c), 21.75, 17.60 and 17.61; BFFHZ Q3.1; MO 339541;
  FFWZ Q5.9.

It supersedes §3 of `gq-bh-bh-writeup-state.md` (10:51), which remains the
lessons-by-mechanism summary.

**What this is.**
- This is a ledger of printed problems (Kourovka, arXiv question lists, MathOverflow, Oberwolfach
  reports, conjectures stated in papers) that the BH lanes answered today. Each entry gives its
  source, our answer, its node and its review status.
- It then summarizes the general mechanisms the day produced, and the claims that were corrected.

**What it is not.** Nothing here has had an external review. Priority checks were bounded to arXiv
(no MathSciNet or zbMATH), and no entry claims novelty. The root `boone-higman-conjecture` is
**OPEN**.

**Review tags.**
- **[R]:** passed a swarm referee pass. The referees are gq-referee-a (proof gaps), gq-referee-b
  (citations), gq-referee-c / bh-referee-c (independent second pass), and the adversarial referee
  lanes bh-ref-kourovka-a/b and bh-ref-misc.
- **[IC]:** passed an internal adversarial check by a different lane, with a verdict artifact on main:
  bh-refute, bh-free-10, bh-free-43 or bh-verify-*.
- **[LP]:** checked only by the lane that wrote it. Several node texts still say "not reviewed" even
  though an [IC] artifact exists; the tag here follows the artifact.

## 1. Scoreboard

| | Refereed [R] | Checked [IC] | Lane only [LP] | Total |
|---|---|---|---|---|
| Printed problems answered in full (§2) | 12 | 10 | 0 | **22** |
| Printed problems answered in part (§3) | 0 | 2 | 8 | **10** |

Counting conventions:
- Both parts of the MO 339541 row are refereed: the homology and the non-finite-presentation result.
- FFWZ Q5.9 is [R]. Part 2 is conditional on SV_P being finitely presented (§2).
- Worked-on problems that stay OPEN are listed but not counted. These include Kourovka 17.58, and
  Kourovka 21.140, which is reduced to one premise (§4).
- The literature asserts that T_{2,3}, T_τ and V_τ are finitely presented, so they are not counted
  either (§5).

Prior and parallel work is credited in §0.

## 0. Credits: prior and parallel work

We want to credit others generously. The answers below stand on the following work, and several
were found in parallel.

**Parallel work on the Kourovka Notebook.**
- van Doorn, Judin, Monticone and Morrison, arXiv:2607.17477 (v1 20 July 2026, v2 26 July 2026),
  answer eight Kourovka problems: 3.46, 18.50, 19.25, 20.125, 21.8, 21.24, 21.147 and 21.150.
- There is no overlap with the problems listed here (bh-openq-lists, `gq-bh-openq-lists.md`).
- Their 21.8, on class transpositions of bounded modulus generating S_{lcm(2..k)}, is the closest
  neighbor of our CT_P(Z) work. Pan proved it independently. Our 21.75 node cites the paper.

**Prior work that answers or contains our statements.**
- Kochloukova and de Sousa Luiz, arXiv:2509.05798 (September 2025), Examples item 2, show that
  Baumslag's group is not self-similar. This predates main's
  `baumslag-char-zero-metabelian-group-is-not-self-similar` (09-12).
- They also conjecture NO for Kourovka 21.41.
- Garrido and Reid, arXiv:2501.00908v1, Corollary `cor:group_expansive_iff_alternating_compactly_gen`,
  already contains the minimal case of the Matui reduction step "finitely generated alternating full
  group ⇒ expansive" (`free-action-fg-alternating-full-groups-force-expansivity`).
- Rungtanapirom, Stix and Vdovina, arXiv:1808.03290, Corollary cor:pi1ofdouble: our RSV-doubles
  answer is immediate from it.
- Kharlampovich, Myasnikov and Sapir answered Kourovka 5.15. We only record that answer.
- Hyde and Lodha constructed the finitely presented infinite simple group behind lean-eval
  `higman_infinite_simple`. Our part is a formalization.

**Work our proofs rest on, read at source by the lanes.**
- Kohl problems:
  - Matui 1210.5800 (`simple2`, `iso2`) and Li 2110.04505 (Cor. `OneVertex`);
  - Li 2209.08087 (`AHConj`) and FKPS 1808.07807;
  - Adamczewski–Bell 1303.2019 and Bell's generalized Cobham theorem (17.57);
  - Kari–Ollinger, MFCS 2008, Theorems 3 and 6 (21.74), and Morita, TCS 168 (1996) (21.73);
  - Rubin–Matui, as read in Matte Bon 1801.10133v2 (17.58-adjacent);
  - Kohl's own RCWA theory and package.
- Twisted Brin–Thompson groups:
  - Belk–Zaremsky 2001.04579, including its Stein complex and `lem:VE_conn`;
  - FFWZ 2603.24687 (Def. 1.3, Prop. 4.17, Cor. 4.18);
  - BFFHZ 2503.21882 (Theorems C and E, Cor. F), and Zaremsky 2405.18354 (Prop. 5.5 and the
    product and wreath constructions).
- FFWZ Q5.9: Scott's finite presentation theorem for Röver–Nekrashevych groups, and
  Bartholdi–Mitrofanov arXiv:1710.10109, Theorem A''.
- RSGs and Stein groups: BBMZ 2309.06224 (Theorem A and the RSG machinery), and Tanner 2312.07375
  (simplicity, and the AH sequence as he states it).
- Matui's question: Matui 1602.00383, Ma 2209.00580, Gordon–Vershik, and Kerr–Nowak.
- Reid's group: Cornulier–Guyot–Pitsch math/0511714, Prop. 2.2.
- Tarocchi 2310.14660 for G_3. Our node adds the one missing step to results imported from his
  paper.
- Mallery–Zaremsky 2202.00822 and P. Hall's extension lemma for Q5.13 and Q3.18.
- Euclidean buildings: Ciobotaru–Le Bars 2601.13092.
- Others: Clapham's embedding theorem (MO 412219), and Salo's conveyor-belt embedding (RAAGs in 2V).
- Stein, Martínez-Pérez–Matucci–Nucinkis, Burillo–Nucinkis–Reeves, Cleary, Brown's criterion and
  Bieri–Strebel, for T_{2,3}, T_τ and V_τ (§5).
- Bartholdi–Virág (the Basilica HNN extension) and Cannon–Floyd–Parry (the facts about F) for
  Kourovka 21.140 (§4).

Not counted:
- literature answers we recorded (Kourovka 5.15, via Kharlampovich–Myasnikov–Sapir);
- reformulations (§4);
- class-level results with no printed question behind them (§5);
- the gq swarm's overnight answer to Kourovka 14.10(c) = BBMZ Problem 2.7 (`gl-n-q-explicit-natural-fp-overgroup`, refereed), listed in §5 for completeness.

## 2. Printed problems answered in full

**Kohl's class-transposition problems (Kourovka Notebook, 21st issue, source `gq/src/kourovka/21tkt.tex`).** One mechanism answers all of them: CT_P(Z) is identified as the topological full group of an explicit one-vertex (|P|+1)-graph. That import brings in Matui's isomorphism rigidity and Li's finiteness at once.

| Problem | Our answer | Node | Review |
|---|---|---|---|
| 17.57: is Out(CT(Z)) = C_2? | **Yes**, generated by n ↦ −n−1. Also Out(CT_P(Z)) = C_2 for every nonempty P (`out-ct-p-z-is-c2`, [LP]) | `out-ct-z-is-c2` | [IC] bh-free-43 PASS |
| 17.59: is CT(Z) the group of RCWA permutations fixing N_0? | **Yes**; an elementary proof of the key step is `piecewise-canonical-permutations-are-transposition-products` | `ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers` | [IC] bh-free-43 full-group check PASS |
| 17.60: are the CT_P(Z) pairwise non-isomorphic? | **Yes**, for finite and infinite P. A second, independent proof for finite P: `gq-bh-bh-free-11-ct-p-z-second-proof.md` | `ct-p-z-groups-are-pairwise-nonisomorphic` | [R] bh-ref-kourovka-a PASS with minor gaps (5821ec240) |
| 17.61: is CT_P(Z) finitely presented for finite P? | **Yes**, and it is simple and F_∞. An explicit class-transposition presentation (`ct-p-z-has-a-finite-class-transposition-presentation`) is still OPEN | `ct-p-z-is-a-one-vertex-k-graph-full-group` | [R] PASS (4697bc8f5), conditional on the published Li / Matui / FKPS theorems. For 17.61 alone, only Li's Cor. OneVertex is needed, given CT_P(Z) = PC. Also [IC] bh-free-43 PASS |
| 21.73: is conjugacy in CT(Z) decidable? | **No**, already in CT_{3,5,7,11,13,17}(Z), even with conjugators from RCWA(Z). The node's smaller set {3,…,13} needs Morita's theorem for 2-counter machines from an initial configuration, which the referee could not confirm | `ct-z-conjugacy-problem-is-undecidable` | [R] bh-ref-kourovka-a PASS with minor gaps (5821ec240), conditional on Morita (TCS 168, 1996), which was not read at source |
| 21.74(b),(c): decide "only finite cycles" and "no finite cycles" | **Both are undecidable** | `ct-z-finite-cycle-problems-are-undecidable` | [R] PASS (fac0259d6), conditional on Kari–Ollinger's Theorems 3 and 6, used as printed. Their MFCS 2008 paper gives proof sketches only. |
| 21.75 | **Negative**: CT_P1 and CT_P2 always generate CT_(P1∪P2) | `ct-p1-and-ct-p2-always-generate-ct-p1-union-p2` | [R] bh-ref-kourovka-b PASS (fac0259d6), with two independent proofs |

**Kohl problems worked on and still OPEN (not counted).**

| Problem | What was found | Node | Review |
|---|---|---|---|
| 17.58: does CT(Z) have subgroups of intermediate growth? | Not settled. CT(Z) and every CT_P(Z) have nontrivial isotropy only at rational points, so none is isomorphic to nV (n ≥ 2) or to any full group of a product of SFTs (by Rubin–Matui). The full-group route needs an embedding of 2V (or of [[X]] for a minimal subshift X) into CT(Z), which is undecided | `ct-p-z-is-not-a-product-shift-full-group` (ad962750f) | [LP] |
| 21.74(a) | See §3 | | |

**Other printed problems.**

| Problem (exact source) | Our answer | Node | Review |
|---|---|---|---|
| Belk–Zaremsky Conjecture H (arXiv:2001.04579, l.218) | **Yes**: for faithful actions, SV_G is F_n iff the action is (A_n), and FP_n iff (HA_n) | `twisted-brin-thompson-type-fn-criterion` | [R] a, b, c PASS |
| FFWZ §1.2 conjecture (arXiv:2603.24687), for abstract SV_G | **Yes**: fp iff [A_2], F_n iff [A_n], FP_n iff [HA_n] | `abstract-twisted-bt-type-fn-criterion` | [R] a, c PASS |
| BFFHZ Q3.1 (arXiv:2503.21882v2): is PBH closed under graph products? | **Yes.** Proved 09-14 and re-verified end to end today | `pbh-class-closed-under-graph-products` | [R] PASS (4697bc8f5), checked against BFFHZ Theorems C and E in the TeX. Also [IC] bh-free-10 PASS |
| BFFHZ Q3.3 (same paper) | **No**: the mixed identities of Thompson's T are not finitely normally generated. The reformulation is `bffhz-q33-is-normal-finite-generation-of-mixed-identities` | `thompson-t-mixed-identities-are-not-finitely-normally-generated` | [IC] bh-refute PASS |
| Zaremsky, Oberwolfach Report 26/2018, Question 110 | **No**: every homomorphism from Higman's group to Monod's H(R) or to a Lodha–Moore group is trivial | `higman-group-embeds-in-no-lodha-moore-or-monod-group` | [IC] bh-refute PASS |
| MathOverflow 412219: is E(G) recursively presented for fp decidable G? | **No.** A second route now follows from the FFWZ Q5.9 witness through the implication `nonrecursive-a2-kernel-makes-e-of-wreath-not-rec-presented` ([LP]) | `fp-decidable-group-whose-e-is-not-recursively-presented` | [IC] bh-refute PASS |
| FFWZ Q5.9 (arXiv:2603.24687v2): can every type [A_2] pair (G, K) be sharply embedded in one whose kernel is finitely normally generated? And the analogous question for fp relatively simple pairs | **No to both parts.** Scott's theorem needs no faithfulness, so the abstract Röver–Nekrashevych group of a free group with a Bartholdi–Mitrofanov recursion is fp. Its clopen action is of type [A_2] with a non-recursive kernel, so the kernel cannot be removed. Its simple quotient has unsolvable word problem. This refutes `a2-action-kernels-are-recursive` and shows that kernel removal cannot carry (relPBH) ⇒ (PBH) | `a2-pair-with-non-removable-kernel-exists`, `fp-relatively-simple-pair-with-unsolvable-simple-quotient`, `some-a2-action-has-a-nonrecursive-kernel` (25056ab91) | [R] bh-ref-ffwz PASS (9dfa9e546). Part 1 is unconditional. Part 2 is conditional on SV_P being finitely presented, via FFWZ Theorem B, which has a recorded gap (§6), or via the repo's refereed `abstract-twisted-bt-type-fn-criterion`. Applying that criterion here is the next review |
| MathOverflow 339541 (C. Reid, 2019): basic properties of the d = 0 Higman–Thompson variant | Abelianization Z ⊕ Z/2, and groupoid homology Z, Z, 0, 0, …. **Also, Reid's group and its derived group are not finitely presented:** a finitely presented emitter full group forces an isolated vertex group, and Z is not isolated | `reid-higman-thompson-variant-d-zero-abelianization`; non-fp: `free-product-emitter-full-groups-need-isolated-vertex-groups`, `stabilizer-engines-are-fp-only-over-isolated-groups` (5d7507af3, bb487abce) | Homology: [R] bh-ref-misc PASS (6a0a3642f), covering the parent homology node; two cosmetic gaps recorded. Non-fp: [R] bh-ref-engines PASS (a23f54860). The isolation theorem has two independent proofs. A transport-lemma statement was repaired, with no conclusion changed |
| Tarocchi (arXiv:2310.14660v3, l.1604–1605): is [G_3, G_3] simple? | **Yes**, and so is [G_n, G_n] for every n ≥ 3 | `dendrite-rearrangement-group-g3-has-simple-commutator-subgroup` | [IC] bh-refute PASS |
| Lodha (arXiv:1710.06220v2, l.1700–1702): is S 2-generated? | **Yes**, as is every f.g. simple circle group containing T. His second question, the minimal number of relations, is not addressed | `lodha-simple-group-s-is-two-generated` | [IC] bh-refute PASS |
| Kohl's factorization conjecture (RCWA package manual, ch. 2) | **Yes**: every RCWA permutation of Z is a product of class shifts, class reflections and class transpositions | `rcwa-z-generated-by-class-shifts-reflections-transpositions` | [R] bh-ref-misc PASS for the deduction (6a0a3642f). It is immediate from 17.59 and the elementary piecewise-canonical node, so the credit is "observed", not a new theorem |
| Mallery–Zaremsky Q3.18 (arXiv:2202.00822v2), as stated | **No**: there is an infinite, not f.g., shift-similar group that is not strongly shift-similar. The f.g. form is OPEN | `infinite-shift-similar-groups-need-not-be-strongly-shift-similar` | [IC] bh-refute PASS |
| Almeida–Dantas–de Oliveira-Tosti (arXiv:2609.01868), Q1.1 | **No**: Z wr_X PSL_2(Z[1/2]) is not RF, so it lies in no self-similar group. It does satisfy BH (§5) | `z-wr-psl2-z-half-is-not-residually-finite` | [IC] bh-refute PASS |
| Rungtanapirom–Stix–Vdovina (arXiv:1808.03290, l.754): are the doubled lattices virtually simple? | **No, never.** This closes that route to Kourovka 21.46 | `rsv-quaternionic-doubles-are-never-virtually-simple` | [R] bh-ref-misc PASS (6a0a3642f), with Step 1's universal-cover misnaming fixed. It is immediate from RSV's own Corollary cor:pi1ofdouble, so the credit is "observed" |
| Llosa Isenrich–Schesler–Wu Q1.11 (arXiv:2510.01952v1, l.302, `quest:embedding`): does every f.g. linear group embed in a f.g. self-similar group? | **Yes**, over any field, and even in a finitely presented self-similar group | `fg-linear-groups-embed-in-fp-self-similar-groups` | [IC] bh-verify-linear PASS covers every step (coordinates, finite presentation of E_N(R) and R^N ⋊ E_N(R), self-similarity, in both characteristics); the composition node itself is unreviewed. Q1.10 stays partial (§3) |

## 3. Printed problems answered in part

| Problem (source) | What is settled | Node | Review | What stays open |
|---|---|---|---|---|
| Kourovka 21.74(a) (Kohl) | Permuting a residue partition is r.e., holds for all torsion, and is not a conjugacy invariant; thin invariant sets cannot be carved. **New (d61d20b6b):** every instance of our (b), (c) and 21.73 reductions is a yes-instance, so those reductions are blind to (a). τ_{1(2),0(4)}τ_{0(2),1(2)} is a no-instance for finite and infinite partitions. Kohl's mixer ψ is a no-instance only under the finite reading | `ct-z-invariant-residue-partitions-are-not-conjugacy-invariant`, `ct-z-residue-partitions-cannot-carve-thin-invariant-sets`, `ct-z-residue-partition-question-finite-vs-infinite-reading` | [LP] | the question itself, under its intended finite reading; the node states the missing steps both ways |
| Mallery–Zaremsky Q5.13 | Yes for fp and for F_m strongly shift-similar G | `fp-strongly-shift-similar-groups-have-fp-houghton-like-groups`, `strongly-shift-similar-type-f-m-passes-to-houghton-like-groups` | [IC] bh-refute PASS | the general case, which is tied to the f.g. form of Q3.18 |
| Zaremsky (arXiv:2201.00711v1, l.495–497): QI embeddings, even into F_∞ hosts? | QI embeddings into fp simple groups for: hyperbolic groups; braid groups and MCGs of surfaces with boundary; Aut(F_n); finite products of these. Cubulated hyperbolic groups go QI into 2V, which is F_∞ | `hyperbolic-groups-undistortedly-embed-in-fp-simple-groups` [IC]; `braid-groups-quasi-isometrically-embed-in-fp-simple-groups`, `aut-free-groups-quasi-isometrically-embed-in-fp-simple-groups`, `products-of-hyperbolic-groups-qi-embed-in-fp-simple-groups`, `virtually-compact-special-groups-undistorted-in-2v` [LP] | [IC] + [LP] | an F_∞ host for every hyperbolic group (`hyperbolic-groups-quasi-isometrically-embed-in-fp-simple-groups` is OPEN); Out(F_n); closed MCGs; CAT(0) |
| Tanner (arXiv:2312.07375): when is D(V(Γ,Λ,ℓ)) fp? | Sufficient condition: slope an (F) unit, in every degree. **Widened (fd9f710c0):** it is enough that β ∈ Z[c] with β^b = c^a for an (F) unit c, via a block recoding of the c-shift. Example: β = θ + 1 = θ³ with θ plastic, whose β-shift is not of finite type, yet D(V(Z[θ], ⟨θ+1⟩, ℓ)) is fp simple | `pisot-unit-slope-stein-groups-are-finitely-presented`, `pisot-stein-groups-with-commensurable-f-unit-slopes-are-fp` | [LP] | a characterization; the necessary side is a computable module (`stein-derived-groups-need-computable-modules`) |
| Matui (arXiv:1602.00383v2, l.1402–1406): are derived full groups of free minimal Z^N actions never fp? | Yes for residually finite actions. **Exact reduction** (f2350f8a4): D([[φ]]) is f.g. iff φ is expansive, i.e. a subshift, and if D([[φ]]) is fp then φ is a minimal SFT | `rf-free-minimal-zn-actions-have-non-fp-derived-full-groups`, `free-minimal-zn-fp-derived-full-groups-live-only-on-sfts` | [LP] | exactly the minimal free Z^N SFTs (N ≥ 2). The first test is Labbé's shift (`labbe-shift-derived-full-group-is-finitely-presented`, OPEN) |
| LISW Q1.10 (arXiv:2510.01952v1) | Yes for f.g. subgroups of GL_n(C) of type FP_2 over no field, e.g. Z wr Z | `non-fp2-groups-are-quasi-retracts-of-simple-groups` | [LP] | the general case (`fg-complex-linear-groups-are-quasi-retracts-of-simple-groups`) |
| BBMZ-hyperbolic Q1.1 (arXiv:2309.06224v3) | Yes for every non-elementary hyperbolic group with a finite-index nontrivial free product, including virtually free groups (trivial nucleus) | `virtually-free-product-hyperbolic-groups-are-contracting-rsgs`, `virtually-free-groups-are-contracting-rsgs` | [LP] | one-ended hyperbolic groups |
| BBMZ-hyperbolic Q1.4 (same paper, l.236) | Yes for contracting RSGs | `contracting-rsgs-have-fp-full-closures` | [LP] | non-contracting fp RSGs (`fp-rsgs-have-fp-full-closures`) |
| BBCMP Q1.16, first part (preprint, author's page) | Low-complexity MCGs are continuous automatic; once-punctured ones asynchronously | `low-complexity-mapping-class-groups-are-continuous-automatic` | [LP] | all finite-type MCGs (`mapping-class-groups-are-continuous-automatic`) |
| BBMZ survey Problem 5.3(10) (CAT(0) groups) | The exotic Ã₂ case: every cocompact Ã₂ lattice, torsion allowed | `exotic-a2-lattices-satisfy-boone-higman` | [LP]; the vertex-free case [IC] | CAT(0) in general, and cubulated (BBCMP Q1.15, OPEN) |

## 4. Reformulations of printed questions (not answers)

- **BBMZ Q1.5 ⇔ PBH, and BBMZ Q1.6 ⇔ BFFHZ Q3.4.** The abstract reading of Q1.6 is answered.
  `bbmz-oligomorphic-and-twisted-questions-are-pbh-forms`, [R] a, b PASS.
- **BFFHZ Q3.3 at rank k** is normal finite generation of k-variable mixed identities. It descends
  to lower ranks. `bffhz-q33-is-normal-finite-generation-of-mixed-identities`, [IC].
- **Cornulier–Guyot–Pitsch Q1–Q4** (arXiv:math/0511714) all stay OPEN. Q1 reduces to Q3 for
  residually solvable groups (`residual-solvability-reduces-cgp-question-1-to-question-3`). There
  are closure results (`ascending-hnn-of-isolated-groups-embed-in-isolated-groups`,
  `fp-groups-with-max-n-are-limits-of-isolated-groups`), all [LP].
- **Kourovka 21.140 (Witzel–Zaremsky) and Zaremsky Problem 2.8 reduce to one premise** (6dc3f9d10).
  The questions: must a torsion-free F_∞ group of infinite cd contain Thompson's F?
  - `thompson-f-free-groups-closed-under-extensions-and-unions` [LP]: groups with no copy of F are
    closed under subgroups, extensions and directed unions, and contain every RF group.
  - So the Bartholdi–Virág ascending HNN extension of the Basilica group is fp, torsion-free, of
    infinite cd, and contains no F.
  - Route `basilica-hnn-fp-infinity-answers-kourovka-21-140`: if that group is FP_∞, both questions
    have answer no. No amenability hypothesis on F is needed.
  - Status: OPEN, pending FP_∞ of the Basilica HNN extension.

## 5. Class-level results (no printed question behind them)

- **T_{2,3}, V_{2,3}, T_τ and V_τ are finitely presented** (8c548b3da, lane bh-near-actions, [LP]).
  - These are proofs written out for statements the literature already asserts. Credit: Stein;
    Martínez-Pérez–Matucci–Nucinkis, arXiv:1309.7858, l.293; Burillo–Nucinkis–Reeves,
    arXiv:2006.02401, l.101 ("by the methods of Stein"); Cleary for F_τ.
  - The tools: `oligomorphic-actions-with-f-n-set-stabilizers-are-f-n`, by Brown's criterion on the
    full simplex. For n = 2 it certifies finite presentation, and hence type (A), from 3-set
    stabilizers. And `circle-pl-groups-inherit-finiteness-from-interval-groups`: under
    Bieri–Strebel (S) and (R), T(A,P) is F_n when F(A,P) is.
  - So T_{2,3} and T_τ are F_∞, and V_τ is fp via the golden Pisot coding (F_∞ for V_τ is not
    proved here).
  - The simple subgroups T_xz and V_xz (BNR) are fp simple groups in B_A, and
    `irrational-slope-v-tau-subgroups-satisfy-pbh` is ESTABLISHED. This bears on BFFHZ Q3.4 for circle
    groups but does not answer it.

- **Every discrete cocompact group on a locally finite thick irreducible Euclidean building of
  dimension ≥ 2, of any type, lies in B_A:** `euclidean-building-lattices-lie-in-permutational-bh-class`,
  [IC] bh-verify-euclid PASS. It is conditional on Ciobotaru–Le Bars (arXiv:2601.13092).
  - So the non-RF Titz Mite–Witzel C̃₂ lattices and their simple kernels are in B_A.
  - Correction: at `ddeea47ea` this bullet said every recorded fp simple group was in B_A. That
    was premature: W, W_(P,ℓ) and the odd-prime Leavitt tensor units were still outside. They
    entered at `2d9a15b01` (14:58), through `twisted-integral-affine-groups-lie-in-the-permutational-class`
    and `projective-leavitt-tensor-units-lie-in-the-permutational-class`, both [LP] (see §7a).
- **Other classes placed in B_A or BH today:**
  - cocompact lattices on products of trees, torsion allowed (`cocompact-tree-product-lattices-lie-in-type-a-class`, [IC]);
  - RCWA groups over Z, class-number-one rings, F_q[t] and Z_(π) (`rcwa-groups-satisfy-permutational-boone-higman`, [R] a, [IC]);
  - limit groups over torsion-free hyperbolic groups ([IC]);
  - Z wr_X PSL_2(Z[1/2]) and the non-RF double of PSL_2(Z[1/2]) (`double-of-psl2-z-half-along-psl2-z-lies-in-b-a`, [LP]);
  - unit groups of L_p ⊗ L_p for every prime p (`leavitt-tensor-unit-groups-lie-in-the-permutational-class`, [LP], landed after the 14:15 restart).
- **Linear hosts.** W is fp, simple and contains every GL_n(Z) ([IC] bh-verify-W PASS).
  St_10(R_L) is an explicit fp group containing every GL_n(Q) (Kourovka 14.10(c) = BBMZ 2.7; gq
  swarm, refereed). GL_n(Q) in an fp **simple** group, BBMZ 5.3(5), is OPEN.

## 6. Possible errors found in the literature (lane findings, for expert confirmation)

- **FFWZ 2603.24687, Lemma 4.9(i),** fails for non-faithful actions
  (`ffwz-nonfaithful-stein-stabilizers-contain-canonical-kernel`). Referee c confirmed the gap is
  genuine. Our proof of their §1.2 conjecture avoids it.
- **Belk–Zaremsky `lem:VE_conn`:** the conclusion is true, but the proof has two errors. The
  node's N1 note fixed one, and referee c supplied a repair for the second
  (`gq-bh-referee-c-conjecture-h-and-ffwz.md`, W1).
- **Kojima–Sheng 2603.18410:** the two-generator torsion criterion is false in V ([R] a).
- **arXiv:2609.01868:** in the Theorem A representation every lamp acts the same way, so it is not
  faithful. Their Theorem B item (3), deduced from Theorem A, fails with it.
- **Amir–Lazarovich 2605.09493,** Discussion l.2386–2407: their fp simple lattices have torsion,
  hence infinite cohomological dimension (`amir-lazarovich-simple-lattices-have-torsion`, [LP]). So
  they do not answer Kourovka 21.46, which stays OPEN.

## 7. The mechanisms: what the day teaches about general BH

**M1. Wrapper ∘ actor, and the wrapper is solved.**
- Conjecture H and the FFWZ conjecture (§2) make SV_G finitely presented (and F_n) exactly when the
  action is of type [A_2] (resp. [A_n]).
- Cuntz stabilization gives type (A) on clopens. Li's degree-map theorem gives F_∞.
- Lesson: a proof of BH is entirely the construction of an **actor**, a finitely presented group
  with a type (A) action containing the input.

**M2. Carrier principle (SYNTHESIS v4).** Complexity and coarse geometry must both be carried by the
acting group Λ.
- Finite-state codings cap the word problem at 2^{Cl²}, and coding isotropy acts residually finitely.
- Move-table units force a translation-like action, so sep(input) ≲ sep(Λ).
- Non-amenability is forced three times: Stein–Farley cocompactness, the separation cap, and
  Osajda exactness.
- Lesson: hosts built from fixed finite data specialize and have complexity ceilings
  (`leavitt-square-units-have-conp-parity-p-complete-word-problem`,
  `fp-piecewise-projective-groups-specialize-to-algebraic-data`). So the actor must grow with the
  input.

**M3. Complexity comes from composition, not local data.**
- A fixed fp simple group, CT_P(Z), holds arbitrary reversible Minsky machines as single elements,
  so its element dynamics are undecidable while its word problem is trivial (bh-free-58). The same
  mechanism answers Kourovka 21.73 and 21.74(b),(c).
- SMART renormalization gives BS(1, ±m) ≤ 3V for every odd m ([IC]).
- Meanwhile finite presentation pins enumerations, slopes, germ schedules and normalizers to
  regular form. That is also how Kourovka 17.57 was answered: normalizers are 2- and 3-regular, and
  Adamczewski–Bell then forces affine.

**M4. Quantum rigidity is the crux gate (E2), and there is now a toolkit for it.**
- **Finite presentation is a rigidity certificate.** Only topological freeness is needed, one free
  point per cylinder (`topologically-free-subshift-full-groups-force-quantum-rigidity`, bh-invent-12).
- **Scale collapse.** For an SFT with an injective constant-size block substitution, e.g. DRS
  fixed-point tiles, rigidity is decided at one scale ≤ max(r, 5) (bh-free-12). This turns E2 into a
  finite check.
- **Transport.** Rigidity is stable under products and deterministic extensions.
- **Compression over non-amenable groups.** Free-group boundary shifts are rigid at every scale
  (`free-group-boundary-shift-is-quantum-rigid`), and so is their product over F_m × F_n. So are
  Euclidean building boundary shifts (`euclidean-building-boundary-shifts-are-quantum-rigid`) and Ã₂
  boundary skew shifts. Hyperbolic geometry supplies rigidity.
- **Fold lemma.** Folds and Busemann transplants import the fibre's rigidity problem unchanged. So
  ABHT's F_n × Z SFT is rigid only if its Z² fibre is, and the centrality condition (C) is open.
- **Obstructions.**
  - One finitely supported modification of a minimal SFT kills rigidity (bh-g2-obstruct).
  - Thickness kills two-sided rigidity of flat subshifts in buildings (bh-g2-buildings).
  - Determinism certifies rigidity only without fault slabs in two directions (bh-g2-labbe).

**M5. Finiteness engines without Li's hypotheses (E3 / P2′).**
- **Perron criterion.** Li's (t<d) is the special case w = 1 of "a strictly increasing positive
  weight on cylinder types". A primitive type-substitution matrix with Perron eigenvalue > 1
  supplies the weight (bh-invent-perron). The pointed-cube categories of free cocompact
  cubulations are Li–Garside categories (`pointed-cube-categories-are-li-garside-categories`, [LP],
  landed after the 14:15 restart).
- **Thumann's operad theorem** gives F_∞ from square filling plus a **finite spine** of minimal
  common refinements, with no LCM needed (bh-free-54). It needs only F_∞ transformations, not F_∞⁺
  (bh-invent-07).
- **V-cone sliding.** Relations between elements with disjoint V-supports follow from
  bounded-diameter relators (bh-invent-01). So P2′ splits into V(Λ), which is always fp, and one
  Boolean-power crossed product that carries all the rigidity (bh-free-29).

**M6. Permanence.**
- **Coset wreaths.** Coset-wreath closure ⇔ identity-edge HNN closure ⇔ centralizer realization
  (`pbh-coset-wreaths-iff-identity-edge-hnns`, referee PASS conditional on its literature inputs,
  `4b2fdd3d9`).
  - **Scope:** only **restricted** wreath products, with finitely supported lamp functions. Twisted
    coset lamplighters and unrestricted products are not covered. The BS(1,2) chain failed exactly
    here (§8).
  - The Z wr_X PSL_2(Z[1/2]) lamp wreaths of §5 are restricted, so they are within scope. Their node
    `lamp-wreaths-over-psl2-tree-vertices-lie-in-b-a` has had only a partial check, with no verdict.
- **Graph products** (BFFHZ Q3.1, §2).
- **Self-square hosts.** Every host machine on main contains its own square: the Cuntz cone shift,
  the Leavitt corner map, and the Brin–Thompson clopen stabilizer. So product closure is never a
  separate gate for a constructive route (bh-major-product).

**M7. The actor is never the input.** Type (A) needs f.g. infinite-index subgroups with finitely
many double cosets. Negative curvature forbids them, and so do building rigidity and the structure
of St_N(R_L) (`escaping-invariant-sets-force-infinitely-many-double-cosets`). The QI results in §3
show that coarse geometry is not the obstruction.

**M8. Gate U has an exact interface.** For simple inputs, gate U over a fixed scaffold Λ is a
coarsely dense injective Lipschitz realization of a Schreier quotient of the input in Λ. Kazhdan
inputs need one-ended, uniformly non-amenable scaffolds (bh-gate-u-wobble, bh-invent-09).

## 7a. General mechanisms (today, after 14:15; from board LESSONS.md)

All four are lane proofs [LP] unless marked.

- **Centrality (C) is proved for tree folds.**
  - `extension-rigidity-is-base-centrality-plus-pointwise-rigidity` (bh-free-09): for any SFT
    extension over any group, quantum rigidity ⇔ (C), central base idempotents in every quantum
    family, ∧ rigidity of each fibre relative to its base point. So (C) is the whole E2 content of
    every layered design.
  - `path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid` (bh-g2-abh, 3c8b41742): for path
    folds, (C) holds automatically, because commutation propagates one tree step at a time along the
    backward-arrow chain.
  - So ABHT's F_n × Z SFT is rigid ⇔ its horizontally expansive Z² fibre is. E2 along folds is
    exactly Z² rigidity.
- **P2′b ⇔ FSG(Λ, A).**
  - `gluing-kernels-descend-from-the-full-shift` (bh-p2b-exact): for [[G_V × (Λ ⋉ X)]] with X
    topologically free, the gluing kernel is the image of the full shift's. So P2′b for every
    topologically free subshift over A is one statement about A^Λ.
  - `gluing-kernels-descend-from-the-free-group-full-shift` (bh-one-relator) removes freeness and
    passes to quotients of Λ. The single object A^(F_n) decides P2′b for every subshift over every
    n-generated group.
  - Rigidity (P2′a) lives on X, and exactness (P2′b) lives on the canonical full shift.
- **Product closure and joint embedding hold across the recorded census.**
  - `twisted-integral-affine-groups-lie-in-the-permutational-class`: W and W_(P,ℓ) act with type (A)
    on ordered unit-class partitions.
  - `projective-leavitt-tensor-units-lie-in-the-permutational-class`: the scalars are killed by
    u ↦ u ⊗ (u*)^(-1).
  - So every fp simple group recorded on main is in B_A, and B_A is closed under finite direct and
    free products (BFFHZ Cor. F). Hence JE, SQ and product closure hold among all recorded groups.
  - The Leavitt hosts are fp and simple only modulo the Khanh / Ara–Cortiñas imports.
  - The general statements `fp-simple-groups-have-the-joint-embedding-property` and
    `boone-higman-closed-under-finite-direct-products` stay OPEN. A counterexample must be an fp
    simple group built by neither full groups nor Leavitt tensor units.
- **E1's input half ⇐ (D), a free subshift with decidable language.**
  - `free-products-with-z-inherit-m2-from-decidable-free-subshifts` (bh-g1-universal-point): if A
    carries a nonempty free subshift with decidable language, then A * Z carries an effectively
    closed minimal free subshift. No minimality or universal point is needed in A.
  - So (M2) is a pure effectivity question. (D) itself, `decidable-groups-carry-free-subshifts-with-decidable-language`,
    is OPEN.
  - E1 also needs its square half, the BSS Q:minimal part. bh-g1-bss finds strongly proximal
    geometries (W_3 = Z/2 * Z/2 * Z/2) remove the synchronization obstacle for measured inputs.

**Where this points (SYNTHESIS v4, Track A).**
- The chain: G ≤ G × F₂ ≤ Λ₁ (Clapham, fp, decidable, non-amenable), and Λ = Λ₁ × Λ₁.
- E1: a minimal free SFT X on Λ exists.
- E2: X is quantum rigid. This is the sharpest open gate.
- E3: P2′.
- Then A(G_V × Λ ⋉ X) is an fp simple group of type (A) containing G.
- The recorded conditional theorem: BH ⇐ E1 ∧ E2 ∧ Farrell–Jones with coefficients ∧ Khanh.
- The synthesis lane estimates BH "leaning true, about 65/35". That is an opinion, not evidence.

## 8. Corrections and over-claims (today)

**Failed review, now OPEN (do not cite as results):**
- `higman-chain-group-lies-in-b-a`: "G_1 = BS(1,2) *_Z BS(1,2) lies in B_A" (80ce687aa);
- `baumslag-solitar-chains-of-every-length-lie-in-b-a`: "BS chains of every length lie in B_A" (23e5c5c7d).

Both failed at the Kaloujnine–Krasner step (referee `4b2fdd3d9`). The map lands in the
**unrestricted** product C^(A/C) ⋊ A, since κ_b is nontrivial at every b-fixed coset. The B_A results
cited cover only restricted coset lamplighters. So Higman's group and Baumslag–Gersten get no B_A
vertex group from this route.
- Flag for its owner lane (not edited here): `baumslag-gersten-in-b-a-from-a-root-separated-shift`
  still says the chain node "settles the base K".
- `bs12-base-generator-is-a-centralizer-in-b-a` passed, conditional on two lane nodes, and only for
  the restricted lamplighter.

**Refuted or dead routes:**
- the Houghton lifting reduction: `houghton-like-envelopes-lift-finite-presentation-from-germs` is
  REFUTED by a free-shift enumeration, and `decidable-houghton-envelopes-via-generic-nu-and-lifting`
  is DEAD;
- the spherical-Artin Garside route: `garside-odometer-groups-have-simple-finite-index-commutator`
  is REFUTED;
- the symplectic rational-projective route for Deligne's lattice: the class survives
  (`deligne-class-survives-on-standard-rational-projective-hosts`);
- the Amir–Lazarovich and RSV routes to Kourovka 21.46 (§2, §6).

**Retracted in coordinator reports to the user:**
- "C_n linear" as new: it has been known since 1976;
- a K_2 bypass for GL_n(Q);
- calling the Belk–Zaremsky statement a theorem before it was proved;
- a 3-manifold candidate block that is not free;
- the MO 491978 candidate, which is not finitely presented.

**Mislabels to avoid:**
- the quasi-retract result `non-fp2-groups-are-quasi-retracts-of-simple-groups` answers LISW Q1.10
  (TeX l.289), and only for f.g. groups of type FP_2 over no field. Earlier summaries called it
  "LISW Q1.11", which was a mislabel. Q1.11 (l.302, `quest:embedding`: "Does every finitely generated
  linear group embed into a finitely generated self-similar group?") is a different question. It is
  answered yes, even with a finitely presented self-similar group, by
  `fg-linear-groups-embed-in-fp-self-similar-groups`. That is a lane composition of nodes on main, not
  reviewed as a composition; it is now a row of §2. The numbering was checked against the
  v1 e-print (sha256 `6d7b8e1e…a4ee6`): the theorem counter is shared, and section 1 runs Thm 1.1,
  Cor 1.2, Cor 1.3, Thm 1.4, Rem 1.5, Q 1.6, Cor 1.7, Cor 1.8, Prop 1.9, Q 1.10, Q 1.11, Q 1.12;
- BFFHZ Q3.1 was proved on 09-14 and only re-verified today;
- Kourovka 5.15 is a literature answer;
- lean-eval `higman_infinite_simple` is a formalization of Hyde–Lodha, not a mathematical solution;
- Kohl's factorization and the RSV doubles are "observed" rather than new theorems. Each follows at
  once from a statement already in the source, or in a node landed an hour later (bh-ref-misc lesson);
- the 21.73 host set is {3,5,7,11,13,17}, not {3,…,13} as the node title still says (5821ec240).

**Node-level fixes:**
- the Mallery–Zaremsky Q5.13 node had claimed an arXiv check that was never run, and it now says so;
- bh-verify-cbm repaired one false lemma;
- bh-verify-master-3 corrected the "Instances" and "Lesson" framing;
- the quadratic IET claim is restricted to norm −1 fields.

**Still OPEN, though easy to misread as settled:**
- Kourovka 7.19, 17.58, 21.46, 21.74(a) and 21.140 (reduced to FP_∞ of the Basilica HNN extension);
- BBCMP Q1.15 (cubulated);
- BBMZ-hyperbolic Q1.1 (one-ended case) and Q1.2;
- Zaremsky 2.19(a) and (c);
- FFKLZ Q2.4 and BFFHZ Q3.6;
- the f.g. form of Mallery–Zaremsky Q3.18;
- `boone-higman-closed-under-finite-direct-products` and JE in general (they hold only across the
  recorded census, §7a);
- Matui's question, now exactly the minimal free Z^N SFT case (§3);
- GL_n(Q) in an fp simple group.

## Lesson for general BH

Every full answer today came from the same move: recognize the group as the full group of a finite
combinatorial model (a k-graph, a Stein complex, an RSG), and import rigidity and finiteness from
that model. The Kohl problems, Conjecture H, Tarocchi and Lodha are all instances. The open gate E2
is the same move run in reverse. A finitely presented full group certifies quantum rigidity of its
model, so general BH now needs one rigid minimal free model over a non-amenable Λ carrying the
input, and the toolkit of M4 is what builds it.
