# Boone–Higman: master route (synthesis v8, final text, 2026-09-19)

Lead synthesis of the 09-18 BH swarm, lane `bh-synth-lead`.
- **Versions:** v1 12a123bf1, v2 b344473a1, v3 8d0279a62, v4 fa0efca1c, v5 16bd19b7f, v6 b5ad39956,
  v7 a85dd1c95. The first v8 text (09c9d3cf9, 09-18 17:31) covered landings to 17:19.
- **What v8 folds in:** every landing and LESSONS.md entry from 16:58 on 09-18 to the 09-19 restart (§6).
  The final text adds the 17:19–17:33 batch and the 09-19 landings (§0.1), and a ranked list of five open
  problems (§7).
- **Status:** this is a strategy document, not a proof. Cited nodes are mostly unreviewed lane proofs, and
  their status lines govern. Items marked **(synthesis remark)** are my own short arguments, unreviewed. The
  live table is `board/SYNTHESIS.md`.

## 0. Thesis (v8): every route builds type (A) actors, so the wall is complexity, not exactness

### What settled since v7

- **E1: PASS, closed at design level.** Both halves pass: the storage-column (D) and tree gluing (1b697300b), and
  the keyed-slot lift (b5c7787d6). The lift's one gap was repair G1: slot keys must be the level-K macro-tile's
  full input field. G1 and G2 are applied (51666562f), so E1 is closed.
- **P2′b: PASS.** K = 1 for every Λ and X (bd5481ba2), with an independent second proof (9752ecd5d). So the
  gluing layer is automatic and P2′ = P2′a. With exact gluing, N_X fp ⇒ F(T_X) fp. P2′a is a tool, not a gate
  (e12544930).
- **E3′: PASS for tree end-shift hosts** (092c2442f).
- **F₂ × F₂ transplant (★′):** PASS, conditional on the fibre (c626199291).
- **The minimal crossing-wire fibre:**
  - two conditional PASSes (27c8ebe61, f757d5cbc), and a second referee PASS at design level with one layout
    repair (713e29b12);
  - it passes the separability test (c4803daa3).
- **Seed pieces.**
  - PASS:
    - the horofunction lemma for all hyperbolic groups, Kazhdan ones included (f2a29310d);
    - finite-type seeds on Ã₂ lattices (e1de4c7e7);
    - relative seeds glue;
    - BG ∈ 𝒞, proved twice: the real-cut order seed (3ff9b63b2) and BG_n (d1a501256).
  - Claimed: finite-type seeds on C̃₂ (547e567e0) and C̃_n lattices (21cd0dd3e); positive-cone seeds for braid
    groups and Ito amalgams (8fb50b000); core-marked gluing (1c1eb8413).
- **A carrier exists for special cubulated inputs.** Wall chains prove rigidity (f10ba67e9; referee PASS f17e0eff2), so
  surface groups, RAAGs, RACGs and median Cayley graphs are in 𝒞, and tree gluing makes the carrier. But no
  infinite FW group is in a wall member of 𝒞.

### Three facts that move the crux

1. **The plane-lift route to (★′) is blocked.**
   - Transport-coupled lifts are rigid but never minimal for a non-SFT input (b2a87978c,
     `e2-for-plane-lifts-is-clustered-floating-freedom`).
   - Bounded defect freedom kills rigidity (bh-free-09's warning).
   - Varying-skeleton lifts reduce E2 to skeleton rigidity plus centrality (92dfb33c5, Part 4 OPEN). But they
     share the infinite-level degeneracy recorded as open by bh-g1-simulation.
   - One narrow exit stays open (ee75271f2, e5d54e463). In aligned plane lifts the floating data can be neither
     constant nor switch far away, so only an exceptional-key defect survives. The decisive tests are defect
     realizability, and (PF1) plus skeleton rigidity for the Busemann height transplant.
   - **So on the minimal route the CARRIER must be a RIGID SEED on the fp overgroup Λ₀ itself**, followed by
     tree gluing over Λ₀ ∗ Z, unless that one exit works.
2. **(RA) blocks only the minimal-subshift tracks** (4ed22df89, `ra-counterexamples-are-minimal-sets-of-rigid-ambients`).
   - A type (A) action has a coset ambient. That ambient is rigid, since full coset shifts are rigid iff the
     double-coset space is finite, which is the pair condition of type (A) (696c37d57). It is also topologically
     free and non-amenable, but it is never minimal.
   - Its host is the twisted Brin–Thompson group SV_Λ, which is finitely presented by Conjecture H (PASS).
   - So the **permutational route escapes the exactness wall.**
   - Also: the Arzhantseva–Osajda wall-orientation lead weakens. Non-exact small-cancellation walls are not
     locally short, so the wall ambient is not rigid at any scale, conditional on quasi-isometrically embedded
     walls (2b88c6f58).
   - (RA′) reduces to one-ended groups (6a95ce886).
3. **Every constructive route outputs a type (A) actor.**
   - The minimal route does: fp V-stabilized full groups of minimal actions have type (A) actions
     (`fp-v-times-minimal-action-full-groups-have-type-a-actions`).
   - The ring route is expected to. This is proved for L_p ⊗ L_p
     (`leavitt-tensor-unit-groups-lie-in-the-permutational-class`, conditional on Khanh). The argument transfers to
     Leavitt-type unit groups that contain a clopen-transitive Brin–Thompson group (bh-major-product's lesson), but
     that is not a theorem for general `(B ⊗ L)^×`.
   - The permutational route does so by definition.
   - So a complexity cap on type (A) actors caps every route (synthesis remark).

### 0.1 After 17:19: four more facts that sharpen the crux

4. **Seed full groups are highly transitive actors, and their hardness is seed evaluation** (2efad1a6f,
   `seed-full-groups-act-oligomorphically-on-the-seed-orbit`).
   - A dense orbit of isolated points puts all its finitary permutations into the full group. So the full group
     of a seed SFT acts faithfully and highly transitively on the seed orbit: isolation buys oligomorphy.
   - Its orbit problem computes the seed configuration along words.
   - So the two routes of fact 3 meet at one object: **HARD-(A) ⇐ a seed whose forced configuration is hard to
     evaluate, and whose V-stabilized full group is fp with one fg stabilizer.**
   - A CAP that bounds only WP(Γ) for Γ ∈ 𝒞 does not bound these actors. The relevant cap is on seed
     evaluation, which the forcing radius controls (971d52e2f).
   - Rigid anticipation, i.e. non-local forcing, needs scale-bounded fault detection (same landing).
5. **Rigidity without walls: every hyperbolic group, Kazhdan ones included, lies in 𝒞** (37abcc802,
   `hyperbolic-groups-lie-in-the-rigid-compactification-class`; lane proof, unreviewed).
   - Gromov-product drop events form non-degrading monotone chains along geodesics, and the target squeeze
     transports letters along them.
   - With tree gluing, every hyperbolic Γ gives a carrier on Γ ∗ Z. So property (T) is no obstruction on the
     dynamics side.
   - Likewise, the Roller compactification of every free cocompact cube complex is rigid (66ad78494):
     compression passes from trees to cubes exactly. It needs uniformly coarsely connected walls, which
     Osajda-type walls lack.
   - The canonical inputs H_Γ are not hyperbolic, so for them the question is geometric: an fp overgroup with an
     anchored-drop, unique-sink compactification. The next candidates are relatively hyperbolic overgroups
     with H_Γ parabolic.
6. **The permutational route is constrained by double cosets** (11aa257f0,
   `type-a-stabilizers-are-hyperbolically-full`).
   - Take a type (A) point stabilizer with infinite orbit, and any non-elementary action on a hyperbolic space.
     The stabilizer is never elliptic there, and never has a quasiconvex orbit with non-full limit set.
   - So locally quasiconvex hyperbolic groups have no type (A) actions, and Higman envelopes have none induced
     from their vertex groups.
   - For Osajda's input, orbit finiteness comes from Hull–Osin (conditional). The whole difficulty is one
     finitely generated, hyperbolically full stabilizer in an fp overgroup. One success gives the first
     finitely presented simple non-exact group.
7. **(RA) is a finite-window statement** (45b0b6895,
   `rigid-subshift-amenability-from-coherent-variation-caps`).
   - Reiter functions come from the variation caps of each point's modification cloud. They work exactly under
     cap coherence (CC). So (RA′) asks whether minimality plus rigidity force the clouds to fellow-travel.
   - The commutant face (c930a62ab): a non-exact commutant of a rigid minimal free Z^d row refutes (RA′), and
     an fp commutant is a carrier. Every rigid row so far has virtually abelian automorphisms (cca4faff6).

### What is LEFT for full BH, precisely

- **Permutational route (P):** BH ⇐ PBH-universality, i.e. every decidable fg G embeds in an fp group with a
  faithful type (A) action. The finiteness step is Conjecture H (PASS), and no exactness or rigidity gate is left.
- **Minimal route (M), for exact inputs:** BH ⇐ RS ∧ ( E3′ for the glued seed host ∨ ( FJ ∧ Khanh ) ).
  - RS means a rigid seed on an fp Λ₀ ⊇ G.
  - E3′ for a seed host reduces to its boundary host (2619448c3, 96c20c080).
  - The crossing-wire host is fp given 3-locality of V-Boolean powers, a Curtis–Tits-type conjecture (0db1cb640).

### THE SINGLE DECISIVE STATEMENT (v8): HARD-(A)

> **HARD-(A)** (`type-a-actors-with-arbitrarily-hard-word-problem`): for every recursive time bound T, some
> finitely presented group with a faithful type (A) action has a word problem harder than T.

- *Equivalent forms* (on main):
  - some fp twisted Brin–Thompson group beats T;
  - the same with the orbit problem in place of the word problem
    (`twisted-brin-thompson-wp-equals-actor-orbit-problem`);
  - some fp simple MIF group beats T (BFFHZ Theorem C).
- *Seed form* (fact 4): HARD-(A) ⇐ a seed SFT whose forced configuration is hard to evaluate, and whose
  V-stabilized full group is fp with one fg stabilizer.
- *It implies Birget's question* (`fp-simple-groups-with-arbitrarily-complex-word-problem`): fp simple groups have
  no uniform complexity bound. That is a necessary consequence of BH.
- *If HARD-(A) is false:* PBH is false. By fact 3, every host the minimal and permutational routes can produce has
  bounded word problem, and so does every ring-route host once the expected transfer holds. The routes die.
  BH would then need a host that is not a type (A) actor (Q3.4 at that input), or it is false.
- *If HARD-(A) is true:* it answers Birget's question, a named problem. The hard actor is the template for
  PBH-universality.
- *Why it replaces v7's ¬(RA):* (RA) now only decides *which* route serves non-exact inputs. HARD-(A) decides all
  of them.

### Where hardness can live: one mechanism on both routes (synthesis remark)

Both routes need a **mortal decider** (termination built into the machine) whose fates propagate along
**directed** chains.

**On the minimal route (seeds):**
- *Forcing radius.* Seed evaluation is bounded by the forcing radius (971d52e2f). Locally forced seeds are capped
  at EXPTIME over polynomial growth, so a hard seed must force non-locally.
- *Where the forcing lives.* Hardness sits at the core and rigidity on the boundary (96c20c080). Non-local forcing
  leaves unforced tails in ∂, so the gate is lemma **CB**: convergent, non-terminating basins in a rigid SFT.
  Seeds compute only where their rogue walks fill space (c1de03335).
- *Geometry.*
  - Finite cuts are finite-state (be079a987), so a computing seed must live in a one-ended group or cross an
    infinite edge interface.
  - Every splitting leaves a pointer in the seed (fcb34cf2d).
  - Mikhailova edges transfer hardness but never create it (637e19dec).
  - Order seeds are computable orders (49c6d7c8e).
- *The rope/halting rung.*
  - Mortal deciders exist for every decidable set, with forcing radius equal to running time (ceaf3f6e9).
  - Mortality forces halting marks only on the genuine sheet (d03fdfb06).
  - Rope readers must couple their chains (27b0124da). The coupled reader links every free chain into one bit and
    is pointwise rigid (1ee36937b).
  - Fate couplings are rigid only along directed implication chains (2e723c93e). Commutation does not propagate,
    but order does.
  - The halting pair (B₂, A_±) is set up (660e18f65).

**On the permutational route (operads):**
- Finite-state propagation caps operad hosts at doubly exponential (6c7a3fd0e), and so do rational frames
  (29c54d27d).
- Branching squares are the only escape (704f2a07b). There, Ore is a machine's halting theorem, and the machine
  must be mortal with non-rational frames.

**Design target.** A mortal decider whose fate relation is a directed chain, realized in one of two ways:
- as a rigid relative seed for the halting pair: minimal route, lanes on the seed tower;
- as a branching-square machine operad: permutational route.

Either one proves HARD-(A).

## 1. Gate ranking v8

| Rank | Gate | Lanes |
|---|---|---|
| 1 | **HARD-(A):** a mortal decider with directed fate chains, as a rigid relative seed for the halting pair (K_M, R_0) / (B₂, A_±), or as a branching-square machine operad. Seed form: a hard-to-evaluate seed with fp V-full group (2efad1a6f), with lemma CB for its unforced tails | bh-invent-11, bh-invent-03, bh-invent-14, bh-invent-15, bh-free-56, bh-typeA-universal |
| 2 | **PBH-universality:** a type (A) actor over every decidable G. Permutational Higman closure = faithful port gluing (a5f6a15a5); kernel removal by generation (a2f925b55); Q3.4 residue BFFHZ Q3.2 at T | bh-invent-02, bh-typeA-universal, bh-ffwz-q59 |
| 3 | **Rigid seeds for non-hyperbolic Kazhdan inputs:** hyperbolic groups are claimed in 𝒞 (37abcc802). Left: the Ã₂/C̃_n perfect boundaries, where midpoint coverings fail (eb4d1b0bf); relatively hyperbolic overgroups with H_Γ parabolic | bh-g2-buildings, bh-emitter-b, bh-invent-13 |
| 4 | **(RA′) at one-ended non-exact groups:** cap coherence (45b0b6895); minimal boundary subsets of Osajda-type walls (66ad78494); non-exact commutants of rigid rows (c930a62ab). Decides whether route (M) can serve non-exact inputs | bh-star-b, bh-ra-counter, bh-ra-proof, bh-invent-16 |
| 5 | **E3′ for seed and fold hosts:** the boundary reduction (2619448c3); 3-locality of V-Boolean powers (0db1cb640); hyperbolic shadow bases need upstream certification, i.e. vertical gluing (5ea9558cf); the fold host is isolated as a fibre filling (ca8f03208) | bh-invent-11, bh-invent-17, bh-p2b-exact, bh-g2-abh |
| 6 | **Reviews:** hyperbolic groups in 𝒞 (37abcc802); Q1.15 (two conditional PASS: 9580d0563, d6778b5f5); crossing-wire (second PASS with a layout repair, 713e29b12); wall-chain carrier (PASS, f17e0eff2); Kazhdan Ã₂ SW layout FAILED, repair route 6fa01acfb, CMSZ corollary conditional (ba8af62eb); G₁ ∈ B_A FAILED, repair eaca0ed9b | referee lanes |
| 7 | **Imports for the ring route:** FJ, and Khanh (inputs checked against the preprint source, ae8e47a3a) | — |

## 2. Structured classes

- **Cubulated, BBCMP Q1.15:** claimed YES, with two conditional referee PASSes after the repairs (9580d0563,
  d6778b5f5). The link lemma now uses Dickson's lemma in place of a packing number (3d36b55b0).
- **Closed MCG, 5.3(2).**
  - Ore = tree domination (141898aff), and the finiteness-route pieces pass review (b091683019).
  - (SC) is proved at the cell vertices and at the centroid, a hexagonal root system (572c7c7e6). A median can
    fail at an interior vertex only through a badly-cut-creating ancestor (663643ab0).
  - In rank 4, commuting splits have an exotic pinwheel minimal bound (157d529c4). So Thumann finiteness is
    decided by finiteness of pinwheel reconciliations, not by finite spines.
- **H4 / BG, 5.3(9).**
  - **Correction:** `higman-chain-group-lies-in-b-a` and the BS-chain node failed review and are OPEN again.
  - The repair puts the twist in the actor (eaca0ed9b). The twist must be dynamical: a host of G₁ needs a
    2-adic odometer on the base generator's degree-one fixed points (9739e63b1).
  - For comeagre ψ, G₁'s germ models are generically faithful (c538a530d).
  - The port route to BG fails at the dilation centralizer (1887cf483).
  - BH for H4 reduces to one swap involution (fb6908cb0).
- **BBMZ Q1.1 (contracting RSGs):** closed surface groups pass review (0c67e7a29). Right-angled reflection groups
  in H³ are claimed (a39f0aa94).
- **GL_n(Q), 5.3(5).**
  - Track A needs only finite presentation plus rigidity, and K_3 limits higher finiteness (7797bc29f).
  - Divisibility is splitting-rigid: finite-root-prime splittings never create Z_(S) (460956b9d).
  - Automaton groups contain no Z_(S) as translations (2a993fc15).
  - Linear hosts need no Suslin theorem (4220f3e9b).
- **Hyperbolic F_∞.** The nucleus-tile operad is the wrong engine (22fc66382), and reflection-group atoms need
  walls (b6c0036e5). Rigidity is now supplied (fact 5), so the gate is E3′ alone.
- **Soluble minimax / Abels.** Correction (a99547ddf): Abels hosts do not have max-n. Isolation needs one invisible
  corner. Germ hosts for Abels-type inputs need bases with dense orbits of cusps (175698f48).
- **Brin–Thompson structure** (landed from the other session on 09-19):
  - every subgroup of nV has hyperfinite orbit relations (faa887c64);
  - fibred V-towers are distortion-free, so the Heisenberg-in-Brin–Thompson question stays open (5ed07408d).

## 3. Retired in v8, and corrections to v7

- **Retired:**
  - the plane-lift route to (★′), except the exceptional-key defect exit (b2a87978c, 92dfb33c5, ee75271f2);
  - exactness as the decisive wall (4ed22df89);
  - the Arzhantseva–Osajda wall-orientation lead (2b88c6f58, conditional);
  - the SW layout for Kazhdan Ã₂ as written (referee FAIL; repair route 6fa01acfb);
  - the nucleus-tile operad for hyperbolic F_∞ (22fc66382);
  - P2′a as a gate (e12544930);
  - the BG port route (1887cf483);
  - self-similar geometry as an F_n certificate for branch HNN extensions (615d598a5);
  - a uniform lag bound for asynchronous contracting hosts (2b1c3d5d1).
- **Corrections to v7:**
  - "(RA) confines every track to exact inputs" was wrong. It confines only the minimal-subshift tracks; the
    permutational route is untouched (4ed22df89).
  - The decisive statement is restated from ¬(RA) to HARD-(A).
  - G₁ ∈ B_A was listed as established. It is OPEN.
- **Update to v7:** P2′b passes review, so E3′ on the group route is the degree-one horizontal condition, i.e.
  rigidity plus the open rigidity-to-fp step (7797bc29f).

## 4. Assessment

**BH true: leaning yes, about 60/40.**
- **For:**
  - The permutational route escapes the exactness wall, and its finiteness step (Conjecture H) is proved.
  - E1 and P2′b pass review.
  - Rigid seeds are claimed for every hyperbolic group, and proved for wall groups.
  - Seed full groups are highly transitive, so seeds feed HARD-(A) directly.
- **Against:** no type (A) actor with hard word problem is known, and every finite-state mechanism is capped.
- **Most informative next proof:** HARD-(A), in its seed form.

## 5. Named results since v7 (off-route)

- Kourovka 17.61: CT_P(Z) is fp by position shifting, elementary (262cbb354, referee PASS e65b9987f).
- BBMZ Q1.1 for closed surface groups: referee PASS (0c67e7a29).
- MIF for exotic rank-two building lattices, credit Le Bars–Leibtag–Vigdorovich (6adcd5d34).
- T_{2,3} and T_τ are F_∞; Cleary's golden V_τ is F_∞ (c7909ca44).
- Kourovka 20.44: a counterexample needs orbits of unbounded size, and the question is Collatz-hard.

## 6. Reconciliation log (v8, final)

- **To 17:19** (first v8 text): see 09c9d3cf9, §6.
- **17:19–17:33:** 37abcc802, 66ad78494, 45b0b6895, 2efad1a6f, 11aa257f0, 51666562f, ee75271f2, e5d54e463,
  713e29b12, 9c6b77e8b, f17e0eff2, ba8af62eb, ca8f03208, 71c2fcd1f, c06e85518, fe9b06f50, 3d36b55b0, b09168301,
  572c7c7e6, 663643ab0, 6aa2688ed, 3e6dfac7f, e2569d314, 5b30cefdb, 252979610, feaaf2820, 1887cf483, b264684c9,
  460956b9d, a99547ddf, 175698f48, 615d598a5, d8ee63c3b, 0c67e7a29, 6adcd5d34, b6c0036e5, 2b1c3d5d1, 861494c34,
  f3345b0a5, 7f25f45d8, a0adfac69, 2c4373101.
- **09-19:** 262cbb354, e65b9987f, 9353b3295, 4220f3e9b, c538a530d, faa887c64, 5ed07408d.

## 7. Five open problems where one insight could give a beautiful general solve (09-19)

Ranked by (generality of the payoff) × (how close a single new idea is). Each entry names the missing insight and
the lane best placed to find it.

1. **Birget's question** (`fp-simple-groups-with-arbitrarily-complex-word-problem`; Birget, arXiv:math/0310335
   §1). Do finitely presented simple groups have unbounded word-problem complexity?
   - *Why now:* by fact 4, seed full groups are highly transitive actors whose orbit problem evaluates the seed.
     So the question is one object: a rigid seed whose forced configuration runs a mortal decider, with fp
     V-stabilized full group.
   - *Missing insight:* rigid non-local forcing, i.e. lemma CB. Unforced tails must converge without
     terminating, with scale-bounded fault detection (2efad1a6f).
   - *Payoff:* HARD-(A), hence the decisive statement of this synthesis, and a named question.
   - *Lane:* bh-invent-11 (owner of the seed oligomorphy and CB nodes), with bh-invent-03 (mortal deciders).
2. **F_∞ simple hosts for all hyperbolic groups** (the F_∞ half of Zaremsky's question, arXiv:2201.00711
   l.495–497).
   - *Why now:* every hyperbolic group has a rigid SFT compactification (37abcc802), atom configurations have
     finitely many types (af235c6d8), and finiteness is horizontal and one-scale (89fbf22bb, 6dfab238a).
   - *Missing insight:* upstream certification for branching descents, i.e. a vertical-gluing presentation of
     the V-stabilized horofunction-boundary host (5ea9558cf).
   - *Payoff:* F_∞ for every hyperbolic group, Kazhdan ones included, by one mechanism.
   - *Lane:* bh-finf-hyp, with bh-g2-buildings.
3. **Closed mapping class groups** (`closed-surface-mapping-class-groups-satisfy-boone-higman`, BBMZ
   Problem 5.3(2)).
   - *Why now:* Ore is tree domination, and the route's pieces pass review (b091683019). (SC) is proved at cell
     vertices and at the centroid. Its only failure mode at an interior vertex is a badly-cut-creating ancestor
     (663643ab0).
   - *Missing insight:* one Stern–Brocot mediant lemma at interior median vertices in rank three, lifted by rank
     induction. Then finiteness of pinwheel reconciliations (157d529c4).
   - *Payoff:* BH for Mod(S_g), g ≥ 3, via the edge-split operad.
   - *Lane:* bh-major-mcg-2, with bh-free-54.
4. **A finitely presented simple non-exact group** (forced by BH through
   `exactness-separates-boone-higman-iff-fp-simple-groups-exact`; not printed as a question).
   - *Why now:* the permutational route escapes (RA) (4ed22df89), and orbit finiteness at Osajda's input comes
     from Hull–Osin (conditional).
   - *Missing insight:* one finitely generated, hyperbolically full stabilizer in a finitely presented overgroup of
     Osajda's group (11aa257f0), plus kernel removal if it is built by gluing.
   - *Payoff:* a new kind of fp simple group, and the exactness separator settled positively.
   - *Lane:* bh-ra-counter.
5. **Higman's group H4** (`higman-group-satisfies-boone-higman`).
   - *Why now:* G₁'s germ models are generically faithful (c538a530d). The host condition is explicit: a type (A)
     actor whose base generator has a 2-adic odometer on its fixed points (9739e63b1). H4 then needs one swap
     involution (fb6908cb0).
   - *Missing insight:* a non-tame base generator with a regular hyperbolic fixed point moved by the dilator.
   - *Payoff:* BH for H4 and, by the shift criterion, for Baumslag–Gersten.
   - *Lane:* bh-major-onerel.

**Runners-up:**
- fg soluble minimax groups (bh-solvable, bh-free-60): a germ base with dense cusp orbits;
- Kourovka 21.140 via FP_∞ of the Basilica HNN extension (bh-openq-lists): a free-action certificate;
- BBCMP Q1.15: closing it needs review, not a new insight.
