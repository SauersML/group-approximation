# Boone–Higman: master route (synthesis v9.2, 2026-09-19)

Lead synthesis of the BH swarm, lane `bh-synth-lead`.
- **Versions:** v1 12a123bf1, v2 b344473a1, v3 8d0279a62, v4 fa0efca1c, v5 16bd19b7f, v6 b5ad39956,
  v7 a85dd1c95, v8 09c9d3cf9 (final text 38000f6a2). Earlier reconciliation logs live in those versions.
- **What v9 folds in:** every landing and LESSONS.md entry from 38000f6a2 to 15:15 on 09-19 (§6), and one referee
  correction to v8 (§0.1). v9.1 (after bh-ref-q11, 3f64521db) relabels the (RA) items: see fact 7. v9.2 adds §0.5.
- **Status:** this is a strategy document, not a proof. Cited nodes are mostly unreviewed lane proofs, and their
  status lines govern. Items marked **(synthesis remark)** are my own short arguments, unreviewed. The live table
  is `board/SYNTHESIS.md`.

## 0. Thesis (v9, unchanged from v8): every route builds type (A) actors, so the wall is complexity

### 0.1 Correction to v8 (referee bh-ref-engines, e046be4f7)

- v8's fact 4 and the seed form of HARD-(A) asked for the **V-stabilized** full group to be finitely presented.
  That group does not act on the seed orbit, so the statement was wrong as written.
- **Correct form.** The **plain** topological full group `[[Γ ⋉ Y]]` of the seed SFT acts faithfully and highly
  transitively on the seed orbit, and its orbit problem evaluates the seed (2efad1a6f, now PASS). So the seed
  form needs `[[Γ ⋉ Y]]` finitely presented, with a finitely generated seed stabilizer. This is exactly the open
  node `hard-evaluation-seeds-with-finitely-presented-full-groups` (7c0c25c19).
- **Two different finiteness gates.** The V-stabilized host appears only on the minimal route (M), where
  E3′(seed) ⇒ E3′(boundary) (2619448c3). The seed form of HARD-(A) needs finite presentation of the plain full
  group. Its natural engine is Farley–Hughes's locally defined groups, and its first non-split test is the
  Houghton group of the free group (7c0c25c19, Attempts 3–4).

### 0.2 What is settled

- **E1:** closed at design level (1b697300b, b5c7787d6; repairs G1/G2 applied 51666562f).
- **P2′b:** PASS, K = 1 for every Λ and X (bd5481ba2, 9752ecd5d). P2′a is a tool, not a gate.
- **E3′:** PASS for tree end-shift hosts (092c2442f).
- **The minimal crossing-wire rigid Z² fibre:** two conditional PASSes, and a second referee PASS with a layout
  repair (713e29b12).
- **Rigid seeds.**
  - PASS:
    - **every hyperbolic group, Kazhdan ones included, lies in 𝒞** (37abcc802, e046be4f7);
    - HL for all hyperbolic groups;
    - Ã₂ finite-type seeds;
    - relative-seed gluing;
    - tree gluing (aa68c0958).
  - Assembled from PASSed inputs: special cube-complex groups lie in fp members of 𝒞 (257360ca8). So the
    special-cubulated CARRIER is unconditional, up to Haglund–Wise.
  - Claims: **BG ∈ 𝒞** by ordered-orbit seeds (8a8a52553); C̃_n seeds; the Toeplitz-enriched order seed for
    (BS(1,m), ⟨a⟩) (ab91e4e2c, checked PASS by bh-invent-14).
- **Hosts.**
  - **BBCMP Q1.15 is ESTABLISHED** (internally refereed): every virtually torsion-free cubulated group embeds in
    a finitely presented simple group (`virtually-torsion-free-cubulated-groups-satisfy-boone-higman`). The
    torsion-allowed F_∞ strengthening is claimed, and referee B PASSed the finite-unit host theorem (a5ccc1aaa).
  - **Euclidean-building lattices** of every type and dimension ≥ 2 embed in F_∞ simple groups (37f53166d; claim,
    under review). This covers the Kazhdan, non-residually-finite C̃₂ lattices.

### 0.3 Seven facts that locate the crux (v8 facts, updated)

1. **The plane lift to (★′) is blocked** (b2a87978c, 92dfb33c5), except one exceptional-key defect exit
   (ee75271f2). So on the minimal route the CARRIER is a rigid seed on Λ₀ itself, followed by tree gluing.
2. **Any form of (RA) blocks only the minimal-subshift tracks** (4ed22df89). Type (A) coset ambients are rigid but never
   minimal, and Conjecture H makes SV_Λ fp. So the permutational route escapes the exactness wall.
3. **Every route outputs type (A) actors.** The minimal route does so by theorem. The ring route does so for
   L_p ⊗ L_p, and is expected to in general.
4. **Seed full groups are highly transitive actors whose orbit problem evaluates the seed** (2efad1a6f, PASS for the
   plain full group). So **HARD-(A) ⇐ one seed SFT, hard to evaluate, with [[Γ ⋉ Y]] fp and a fg seed
   stabilizer.**
   - Where the hardness can go (7c0c25c19): a hierarchical, fixed-point seed that checks one sequence χ_D at every
     level leaves the data free nowhere. So hardness should cost no rigidity beyond the fixed-point skeleton
     (heuristic).
5. **Rigidity without walls** holds for all hyperbolic groups (PASS). For the canonical non-hyperbolic H_Γ the
   question is geometric: an fp overgroup with an anchored-drop, unique-sink compactification.
   - **Correction to v8:** the claim that Osajda-type walls are not uniformly coarsely connected is withdrawn.
     Short relators give short links, so (W1) there is undecided (cf68fcdd7).
6. **The permutational route is constrained by double cosets.**
   - Type (A) stabilizers are hyperbolically full (11aa257f0).
   - Houghton ports also need stabilizers that cross every splitting (c6514e7e6).
   - In a Higman–Clapham envelope, port actions with fg stabilizers are absorbed over the double F ∗_N F′, where
     the input acts freely (dd87ce431). So a permutational Higman embedding must write the relators into the
     permutation structure.
7. **Status of (RA), stated explicitly (v9.1).**
   - **(RA) in its topologically free form is REFUTED on main.** The counterexample is
     `rigid-minimal-topfree-sft-with-non-amenable-point-stabilizer` (lane proof), a minimal, topologically free,
     rigid SFT over `(F_2 × Z) ∗ Z`. It is not free: one point has stabilizer `F_2 × Z`. Its acting group is exact.
   - **The open targets are:**
     - **(RA_free):** every minimal, *free*, quantum-rigid subshift action is topologically amenable;
     - **(RA′):** a minimal, topologically free, quantum-rigid subshift forces the acting group to be exact
       (6a95ce886; it reduces to one-ended groups).
   - Everything below concerns these two. The finite/infinite-fibre split (932c4670b) holds for both:
     quantum rigidity is boundary determination, and every thick cut has at most one free side.
   - *Finite fibres:* an invariant measure exists, so (RA_free) there is a **non-existence** statement. There is
     no rigid, minimal, free, measured action of a non-amenable group.
     - Its commutant form: time lifts are free, so a non-amenable measure-fixing commutant of a rigid, minimal,
       free Z^d row would refute **(RA_free)**. Hence (RA_free) ⇒ rigid uniquely ergodic rows have amenable
       automorphism groups (8fa6f7ccd, referee PASS with this scope correction, 3f64521db).
     - Its residually finite form: nested periodic wire nets, which pay for the rank gradient (e4b6958a0,
       referee PASS).
   - *Infinite fibres:* the target is join-cap coherence (JC′).
     - Plain cap coherence (CC′) is false already on ∂T_m ⊠ ∂T_n (cf68fcdd7).
     - Profinite layers collapse into the equicontinuous factor (ca17dbe93), so an infinite fibre needs a
       connected layer.
   - In infinite fibres, both targets therefore need a finite join dimension plus nearby corners from minimality. Infinite-dimensional
     non-exact wall spaces lack exactly these two things.

### 0.4 What is LEFT for full BH, and the decisive statement

- **(P) permutational:** BH ⇐ PBH-universality. The finiteness step is Conjecture H (PASS).
- **(M) minimal, for exact inputs:** BH ⇐ a rigid seed on an fp Λ₀ ∧ (E3′ for the glued host ∨ FJ + Khanh).
- **DECISIVE STATEMENT, HARD-(A)** (`type-a-actors-with-arbitrarily-hard-word-problem`): for every recursive T,
  some fp group with a faithful type (A) action has a word problem harder than T.
  - It implies Birget's question (`fp-simple-groups-with-arbitrarily-complex-word-problem`).
  - If it is false, every route dies.
  - **Seed form (corrected):** `hard-evaluation-seeds-with-finitely-presented-full-groups`. The plain full group
    `[[Γ ⋉ Y]]` must be fp, with a fg seed stabilizer.

### 0.5 v9.2 additions (summarized from referee verdicts, not re-refereed)

- **T0 is F_∞** (fully refereed: db0daa1547, bb16c96e08, with the Region B repair). T0 is the free-group Houghton
  group, RP_{F_2} of the Cayley tree. It is the first non-split test of the seed form of HARD-(A), and it passes
  the finiteness half of gate 1.
  - HARD-(A) is not thereby given: T0 carries no hard seed.
  - Finite generation of the seed stabilizer is still pending.
- **Complexity caps** (508b190dbb). "Finite type ⇒ finite-state" holds for Farley–Hughes hosts, but only narrowly.
  "Forced self-similar" is false (Farley–Hughes Ex. 4.35). So the cap does not rule out a hard seed with a finitely
  presented full group.
- **Lift-ideal theorem** (c327ef1ef3, PASS in both directions). For finite-state self-similar G, V_d(G) is fp iff
  the relator kernel of G is a finitely generated lift ideal (`rover-nekrashevych-fp-iff-finite-lift-presentation`).
  The action decides finite presentation, not the group.
- **BBMZ Q1.2 (F_∞ hosts for hyperbolic groups).** The level-set join lemma passes (78857ab1ec), a proved case of
  BHM Remark 2.13, together with bounded-RSG F_∞ with integer flux. Surface groups already have hosts via 2V. The
  Z^r extension is next, aimed at Kazhdan hyperbolic groups (§5 item 2).
- **Kourovka.**
  - 19.45 is Collatz-hard (c0b107c65e; credit Kohl's 18.47(b), f8dd716a18).
  - 21.74(a) is decidable for every g in V, for any moduli (19e10ad19b, PASS).
  - 20.44 is reduced to totally consumable groups (06eb299b09, e2b397604f PASS). Frozen tails anywhere give 20.44
    (bc9e6452bf, 643914a82b PASS).
- **(RA_free).**
  - No rigid regular Toeplitz shift exists over surface groups, by the rank-gradient bound (e4b6958a0).
  - Algebraic rows carry rigid free commutants but are never minimal. So the test T1 is an invariant free minimal
    subset of Ledrappier² (54ed6d2fe, in review).

## 1. Gate ranking v9

| Rank | Gate | Lanes |
|---|---|---|
| 1 | **HARD-(A), seed form:** a hierarchical seed checking one hard sequence at every level, with `[[Γ ⋉ Y]]` fp (Farley–Hughes engine; the first test T0 is F_∞, refereed, db0daa1547) and a fg seed stabilizer (pending for T0) | bh-invent-11, bh-invent-03, bh-invent-14, bh-invent-15 |
| 2 | **PBH-universality:** relators written into the permutation structure; ports are translations crossing every splitting (c6514e7e6, dd87ce431, e3897e787) | bh-ra-counter, bh-invent-02, bh-typeA-universal |
| 3 | **Rigid seeds for non-hyperbolic Kazhdan inputs:** the Ã₂ seed boundary is classified as chambers plus panel-tree pointers (7d0b8309d); relatively hyperbolic overgroups with H_Γ parabolic | bh-g2-buildings, bh-free-09, bh-emitter-b, bh-invent-13 |
| 4 | **(RA_free) and (RA′)** ((RA) in topologically free form is refuted), split by fibres: finite fibres, non-existence; infinite fibres, join-cap coherence (932c4670b, cf68fcdd7, 8fa6f7ccd) | bh-ra-proof, bh-star-b, bh-invent-16, bh-ra-counter |
| 5 | **E3′ for seed and fold hosts.** Hyperbolic: crossing, i.e. square filling between descent trees, not upstream certification (3ddb17e3e). Fold: fibre filling (ca8f03208). 3-locality (0db1cb640) | bh-finf-hyp, bh-invent-17, bh-g2-abh |
| 6 | **Reviews:** Euclidean-building F_∞ hosts (37f53166d); BG ∈ 𝒞 (8a8a52553); torsion cubulated F_∞ (a5ccc1aaa, one PASS); CMSZ (ba8af62eb); G₁ repair (eaca0ed9b) | referee lanes |
| 7 | **Imports for the ring route:** FJ, Khanh | — |

## 2. Structured classes

- **Cubulated: BBCMP Q1.15 ESTABLISHED** (internally refereed). The torsion-allowed F_∞ strengthening is claimed
  (de7c42f2a, a5ccc1aaa). The simple-host interface is (C1)–(C3) of the Cuntz–Garside host theorem.
- **Closed MCG, 5.3(2).**
  - **(SC) and (SC₂) are refuted:** a 14-piece and a 17-piece descendant dissection (5a5a8bd32, 2968688a3).
    Every per-node invariant fails at a small, shrinking fraction of nodes, yet the least-damage recursion
    terminates on every test (acb6bede1). So tree domination needs an **amortized** potential. Damage is born at
    parallel splits (165c42817).
  - **Dehn twists are never ports** (e3897e787). No abelian subgroup of Mod(S_g) is cofinite on an infinite
    multicurve orbit. The port must be adjoined: Dehn–Thurston translations in PAff_{6g−6}(Z).
  - So closed-MCG relative PBH is finite presentation of one lattice host
    (`closed-mcg-lies-in-an-fp-dehn-thurston-lattice-host`, OPEN).
- **H4 / BG, 5.3(9).**
  - One gate for H4, BG and GL_n(Q): H4 ∈ B_A ⟸ one full germ extension of V is fp. Its germ group is non-soluble
    and non-RF, so a new germ-group finiteness mechanism is needed (97e463645).
  - Dilating edge axes admit no matched gluing, so seeds, like ports, must be parabolic (3f64a9c66).
  - BG ∈ 𝒞 is claimed through the ordered orbit instead (8a8a52553).
- **Soluble minimax.**
  - Some fg soluble minimax groups have unsolvable word problem (633eb2de3), so the BH statement is restricted to
    decidable ones.
  - S-unit-twisted Prüfer radicals have isolated hosts (23ab3e43b, PASS 6b7f954de).
  - Transcendental corner gluings escape arithmetic hosts (8dd131b96, sketch).
- **GL_n(Q), 5.3(5).**
  - Z_(S) is not additive in automaton groups (5b76fcccb).
  - Contracting groups bound roots at periodic points (8ef5b0e59, 6d6fc15f9).
  - Separable subgroups are Z-semilocal root-closed (fed477ec7).
- **BBMZ Q1.1.** Hyperbolic RACGs with spread nerves are claimed (36cb962fb). The RSG property passes to
  finite-index and quasiconvex subgroups (0866cd809) and to finite-index overgroups (32d05a324).
- **CT_P(Z).**
  - Order is decided by elliptic reduction (2f2045a98, referee c79baedd2).
  - Kourovka 20.44 holds for rank-one slope groups (b4cbe8e26; V case refereed, 0de1f29ea), and mixed-ray frozen
    tails force finite orbits (59f44f3c5).
  - Dickson returns force compressions (62977298e).

## 3. Retired in v9, and corrections to v8

- **Retired:**
  - per-node potentials for tree domination, (SC) and (SC₂) (5a5a8bd32, 2968688a3);
  - plain cap coherence (CC′) (cf68fcdd7);
  - upstream certification as the hyperbolic F_∞ gate (3ddb17e3e);
  - Dehn twists as ports (e3897e787);
  - matched gluing on dilating edge axes (3f64a9c66);
  - absorbing rope readers (1208f63aa);
  - "fg soluble minimax ⇒ BH" without decidability (633eb2de3).
- **Corrections to v8:**
  - The seed form needs the plain full group `[[Γ ⋉ Y]]` fp, not the V-stabilized one (§0.1).
  - The Osajda-walls claim in fact 5 is withdrawn (cf68fcdd7).
  - v8, and the first v9 text, wrote "(RA)" for the open target. (RA) in its topologically free form is already
    refuted on main. The open targets are (RA_free) and (RA′) (fact 7; bh-ref-q11, 3f64521db).
  - §7 items 2 and 3 of v8 named gates that have since moved: upstream certification was not the gate, and (SC)
    is refuted. §5 below restates them.

## 4. Assessment

**BH true: leaning yes, about 60/40.**
- **For:** Q1.15 is established; every hyperbolic group is in 𝒞 (PASS); the permutational route escapes
  exactness.
- **Against:** no type (A) actor with hard word problem is known, and finite-state mechanisms are capped.
- **Most informative next proof:** HARD-(A) in seed form, with the plain full group.

## 5. Five open problems where one insight could give a beautiful general solve (revised)

1. **Birget's question** (arXiv:math/0310335 §1; `fp-simple-groups-with-arbitrarily-complex-word-problem`).
   - *Missing insight:* a hierarchical seed that checks one hard sequence at every level, whose plain full group
     is fp by a Farley–Hughes argument.
   - *First test:* the Houghton group of the free group.
   - *Lane:* bh-invent-11.
2. **F_∞ simple hosts for all hyperbolic groups** (the F_∞ half of Zaremsky's question, arXiv:2201.00711).
   - *Missing insight:* square filling between descent trees at different bases, in Thumann's non-LCM regime. (T)
     forbids walls.
   - *First case:* thick hyperbolic triangle buildings with GQ(q,q) links (3ddb17e3e).
   - *Lane:* bh-finf-hyp.
3. **Closed mapping class groups** (BBMZ 5.3(2)). Either of two insights would do:
   - an amortized damage potential for least-damage tree domination;
   - finite presentation of the Dehn–Thurston lattice host with fg stabilizers.
   - *Lanes:* bh-major-mcg-2 with bh-free-54, and bh-invent-02.
4. **A finitely presented simple non-exact group** (forced by BH).
   - *Missing insight:* one fg, hyperbolically full stabilizer over Osajda's group, with the relators written into
     the permutation structure (dd87ce431).
   - *Lane:* bh-ra-counter.
5. **Higman's group H4.**
   - *Missing insight:* a finiteness mechanism for germ groups generated by a non-soluble implant and a
     non-normalizing shift (97e463645).
   - *Lane:* bh-major-onerel.

**Runners-up:**
- decidable fg soluble minimax groups (bh-solvable, bh-free-60);
- Kourovka 21.140 via the Basilica HNN extension (bh-openq-lists).

## 6. Reconciliation log (v9)

- **Referee:** e046be4f7, aa68c0958, f203e56ab, c49ca4a7a, bbac902d3, b570a6976, a5ccc1aaa, 32d05a324, 458dfc099,
  6b7f954de, 0de1f29ea, c79baedd2.
- **Seeds and HARD-(A):** 7c0c25c19, 257360ca8, 8a8a52553, ab91e4e2c, afa36f070, cfd7ccc17, ce288ce2c, 651a58160,
  dc102427a, 5c85cfc17, 3f64a9c66, 9459f6eaa, 1208f63aa, fe965ca41, 7d0b8309d, 2a9cd8317, 9d9109115, 221511f7b.
- **(RA_free), (RA′):** 932c4670b, e4b6958a0, cf68fcdd7, 8fa6f7ccd, ca17dbe93, c6514e7e6, dd87ce431, 3f64521db.
- **Hosts:** de7c42f2a, 37f53166d, 5ff0e87eb, 3ddb17e3e, 36cb962fb, 0866cd809.
- **MCG:** 5a5a8bd32, 165c42817, 2968688a3, acb6bede1, e3897e787.
- **Classes:** 97e463645, 633eb2de3, 23ab3e43b, 8dd131b96, ab9c1e63e, 7263a4653, 5b76fcccb, 8ef5b0e59, 6d6fc15f9,
  fed477ec7, 2f2045a98, 50b7f0bf8, b4cbe8e26, 59f44f3c5, 62977298e.
