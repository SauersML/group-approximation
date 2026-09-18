# Boone–Higman: master route (synthesis v8, 2026-09-18)

Lead synthesis of the 09-18 BH swarm, lane `bh-synth-lead`.
- **Versions:** v1 12a123bf1, v2 b344473a1, v3 8d0279a62, v4 fa0efca1c, v5 16bd19b7f, v6 b5ad39956,
  v7 a85dd1c95.
- **What v8 folds in:** every landing and LESSONS.md entry from 16:58 to 17:19 (§6).
- **Status:** this is a strategy document, not a proof. Cited nodes are mostly unreviewed lane proofs, and
  their status lines govern. Items marked **(synthesis remark)** are my own short arguments, unreviewed. The
  live table is `board/SYNTHESIS.md`.

## 0. Thesis (v8): every route builds type (A) actors, so the wall is complexity, not exactness

### What settled since v7

- **E1: PASS.** Both halves pass: the storage-column (D) and tree gluing (1b697300b), and the keyed-slot lift,
  conditional on one repairable key-domain gap (b5c7787d6). The repair (G1): the key must cover the whole input
  field. E1 closes with it.
- **P2′b: PASS.** K = 1 for every Λ and X (bd5481ba2), with an independent second proof (9752ecd5d). So the
  gluing layer is automatic and P2′ = P2′a. With exact gluing, N_X fp ⇒ F(T_X) fp. P2′a is a tool, not a gate
  (e12544930).
- **E3′: PASS for tree end-shift hosts** (092c2442f).
- **F₂ × F₂ transplant (★′):** PASS, conditional on the fibre (c626199291).
- **The minimal crossing-wire fibre:**
  - two conditional PASSes (27c8ebe61, f757d5cbc), with one crossing-box fix pending;
  - it passes the separability test (c4803daa3).
- **Seed pieces.**
  - PASS:
    - the horofunction lemma for all hyperbolic groups, Kazhdan ones included (f2a29310d);
    - finite-type seeds on Ã₂ lattices (e1de4c7e7);
    - relative seeds glue;
    - BG ∈ 𝒞, proved twice: the real-cut order seed (3ff9b63b2) and BG_n (d1a501256).
  - Claimed: finite-type seeds on C̃₂ (547e567e0) and C̃_n lattices (21cd0dd3e); positive-cone seeds for braid
    groups and Ito amalgams (8fb50b000); core-marked gluing (1c1eb8413).
- **A carrier exists for special cubulated inputs.** Wall chains prove rigidity (f10ba67e9, under review), so
  surface groups, RAAGs, RACGs and median Cayley graphs are in 𝒞, and tree gluing makes the carrier. But no
  infinite FW group is in a wall member of 𝒞.

### Three facts that move the crux

1. **The plane-lift route to (★′) is blocked.**
   - Transport-coupled lifts are rigid but never minimal for a non-SFT input (b2a87978c,
     `e2-for-plane-lifts-is-clustered-floating-freedom`).
   - Bounded defect freedom kills rigidity (bh-free-09's warning).
   - Varying-skeleton lifts reduce E2 to skeleton rigidity plus centrality (92dfb33c5, Part 4 OPEN). But they
     share the infinite-level degeneracy recorded as open by bh-g1-simulation.
   - **So on the minimal route the CARRIER must be a RIGID SEED on the fp overgroup Λ₀ itself**, followed by
     tree gluing over Λ₀ ∗ Z.
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
- *It implies Birget's question* (`fp-simple-groups-with-arbitrarily-complex-word-problem`): fp simple groups have
  no uniform complexity bound. That is a necessary consequence of BH.
- *If HARD-(A) is false:* PBH is false. By fact 3, every host the minimal and permutational routes can produce has
  bounded word problem, and so does every ring-route host once the expected transfer holds. The routes die. BH would then need a host that is not a type (A) actor
  (Q3.4 at that input), or it is false.
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
| 1 | **HARD-(A):** a mortal decider with directed fate chains, as a rigid relative seed for the halting pair (K_M, R_0) / (B₂, A_±), or as a branching-square machine operad | bh-invent-03, bh-invent-14, bh-invent-15, bh-free-56, bh-typeA-universal, new |
| 2 | **PBH-universality:** a type (A) actor over every decidable G. Permutational Higman closure = faithful port gluing (a5f6a15a5); kernel removal by generation (a2f925b55); Q3.4 residue BFFHZ Q3.2 at T | bh-invent-02, bh-typeA-universal, bh-ffwz-q59 |
| 3 | **Rigid seeds without walls** (minimal route, Kazhdan inputs): horofunction-boundary rigidity of hyperbolic Kazhdan groups (lanes, 2d967a8bf); the Ã₂ perfect boundary (34b85fb09); C̃_n | bh-g2-buildings, bh-emitter-b, bh-invent-13 |
| 4 | **(RA′) at one-ended non-exact groups:** decides whether route (M) can serve non-exact inputs | bh-star-b, bh-ra-counter |
| 5 | **E3′ for seed hosts:** the boundary reduction (2619448c3); 3-locality of V-Boolean powers (0db1cb640); hyperbolic shadow bases need upstream certification (5ea9558cf) | bh-invent-11, bh-invent-17, bh-p2b-exact |
| 6 | **Reviews:** Q1.15 (two conditional PASS: 9580d0563, d6778b5f5); crossing-wire box fix (f757d5cbc); wall-chain carrier (f10ba67e9); Kazhdan Ã₂ SW layout FAILED, repair route 6fa01acfb; G₁ ∈ B_A FAILED, repair eaca0ed9b | referee lanes |
| 7 | **Imports for the ring route:** FJ, and Khanh (inputs checked against the preprint source, ae8e47a3a) | — |

## 2. Structured classes

- **Cubulated, BBCMP Q1.15:** claimed YES, with two conditional referee PASSes after the repairs (9580d0563,
  d6778b5f5).
- **Closed MCG, 5.3(2).**
  - Ore = tree domination (141898aff).
  - Least-damage single cuts (SC) are a Stern–Brocot mediant condition at median vertices (b25d8632d,
    36ab182de).
  - In rank 4, commuting splits have an exotic pinwheel minimal bound (157d529c4). So Thumann finiteness is
    decided by finiteness of pinwheel reconciliations, not by finite spines.
- **H4 / BG, 5.3(9).** **Correction:** `higman-chain-group-lies-in-b-a` and the BS-chain node failed review and are
  OPEN again. The repair puts the twist in the actor (eaca0ed9b). BH for H4 reduces to one swap involution
  (fb6908cb0), and BG to a shift criterion.
- **BBMZ Q1.1 (contracting RSGs):** closed surface groups (6ef4e6c9c, referee wanted), and right-angled
  reflection groups in H³ (a39f0aa94).
- **GL_n(Q), 5.3(5).**
  - Track A needs only finite presentation plus rigidity, and K_3 limits higher finiteness (7797bc29f).
  - Adder hosts are (SL) witnesses (664717421).
  - Automaton groups contain no Z_(S) as translations (2a993fc15).
- **Hyperbolic F_∞.** The nucleus-tile operad is the wrong engine: condition (C) fails for the pentagon group
  (22fc66382). Configuration tiles are needed.
- **Named problems.**
  - Kourovka 20.44 is Collatz-hard (7b84a747f, 1c4a8a43c, 41ac28651).
  - Kourovka 21.46 has inputs and a finite density certificate (cf4c856f6, 4afe513c6).
  - BFFHZ Q3.2 at T: the one-word basis candidate fails (291b9f586).

## 3. Retired in v8, and corrections to v7

- **Retired:**
  - the plane-lift route to (★′) (b2a87978c, 92dfb33c5);
  - exactness as the decisive wall (4ed22df89);
  - the Arzhantseva–Osajda wall-orientation lead (2b88c6f58, conditional);
  - the SW layout for Kazhdan Ã₂ as written (referee FAIL; repair route 6fa01acfb);
  - the nucleus-tile operad for hyperbolic F_∞ (22fc66382);
  - P2′a as a gate (e12544930);
  - G₁ ∈ B_A as established (referee FAIL).
- **Correction to v7:** "(RA) confines every track to exact inputs" was wrong. It confines only the minimal-subshift
  tracks; the permutational route is untouched (4ed22df89).
- **Correction to v7:** the decisive statement is restated from ¬(RA) to HARD-(A).
- **Correction to v7:** G₁ ∈ B_A was listed as established. It is OPEN.
- **Update to v7:** P2′b now passes review, so E3′ on the group route is the degree-one horizontal condition,
  i.e. rigidity plus the open rigidity-to-fp step (7797bc29f).

## 4. Assessment

**BH true: leaning yes, about 60/40.** The number is unchanged, but the risk has moved again.
- **For:** the permutational route escapes the exactness wall, with its finiteness step (Conjecture H) proved.
  E1 and P2′b pass review. Rigid seeds exist over every class tested with walls, and seeds exist (rigidity open)
  over all hyperbolic and Ã₂/C̃₂ groups.
- **Against:** every route produces type (A) actors, and no type (A) actor with hard word problem is known.
  Every recorded class has bounded word problem, and every finite-state mechanism is capped.
- **Most informative next proof:** HARD-(A). Build one mortal decider with directed fate chains, as a rigid
  relative seed or a branching-square operad. It would also answer Birget's question.

## 5. Named results since v7 (off-route)

- Q1.15: two conditional referee PASSes.
- Kourovka 17.61 and the gluing-exactness node: PASS.
- T_{2,3} and T_τ are F_∞; Cleary's golden V_τ is F_∞ (c7909ca44).
- Kourovka 20.44: a counterexample needs orbits of unbounded size.

## 6. Reconciliation log (v8)

- **E1:** 1b697300b, b5c7787d6, dd56f4237.
- **P2′/E3′:** bd5481ba2, 9752ecd5d, e12544930, 092c2442f, 2619448c3, 96c20c080, 0db1cb640, 5ea9558cf, 6dfab238a,
  e7fc5a5be.
- **E2 / lifts:** b2a87978c, 92dfb33c5, c626199291, 27c8ebe61, f757d5cbc, c4803daa3, fd2ba58b6, 6fa01acfb,
  c05f7793b, e1de4c7e7, 4febaf392, f44f9e3be.
- **Seeds:**
  - existence and geometry: f2a29310d, 2d967a8bf, 34b85fb09, 547e567e0, 21cd0dd3e, f10ba67e9, 3624d517a,
    3ff9b63b2, d1a501256, 8fb50b000, 1c1eb8413, fcb34cf2d, be079a987, 637e19dec, 49c6d7c8e;
  - hardness: 971d52e2f, c1de03335, ceaf3f6e9, d03fdfb06, 27b0124da, 1ee36937b, 2e723c93e, 660e18f65,
    bccaf75d3, 5a72aa6a9.
- **(RA):** 4ed22df89, 696c37d57, 6a95ce886, 9180ac550, 2b88c6f58, c930a62ab.
- **Operads:** 6c7a3fd0e, 29c54d27d, 704f2a07b.
- **Q3.4:** a2f925b55, 56b422d20, 291b9f586.
- **Classes:** 9580d0563, d6778b5f5, 141898aff, b25d8632d, 36ab182de, 157d529c4, eaca0ed9b, fb6908cb0,
  6ef4e6c9c, a39f0aa94, 7797bc29f, 664717421, 2a993fc15, 22fc66382, 7b84a747f, 1c4a8a43c, cf4c856f6, 4afe513c6,
  c7909ca44.
