# Boone–Higman: master route (synthesis v7, 2026-09-18)

Lead synthesis of the 09-18 BH swarm, lane `bh-synth-lead`.
- **Versions:** v1 12a123bf1, v2 b344473a1, v3 8d0279a62, v4 fa0efca1c, v5 16bd19b7f, v6 b5ad39956.
- **What v7 folds in:** every landing and LESSONS.md entry from 16:05 to 16:48 (§7).
- **Status:** this is a strategy document, not a proof. Cited nodes are mostly unreviewed lane proofs, and
  their status lines govern. Items marked **(synthesis remark)** are my own short arguments, unreviewed. The
  live table is `board/SYNTHESIS.md`.

## 0. Thesis (v7): existence and rigidity are each closed; the carrier is left, and it meets exactness

### What closed (all modulo review)

- **E1, existence** (74597e3ce; referees bh-ref-e1-a/b running).
  - `minimal-free-sft-overgroups-via-storage-column-free-subshifts` puts every decidable K inside
    `Λ = ((Λ₁ × Z) ∗ Z) × Z²`, which carries a minimal free SFT.
  - Each factor pays for one property:
    - Λ₁ is the Clapham envelope, which gives decidability;
    - the first Z is a storage column, giving (D) (`decidable-groups-times-z-have-decidable-free-subshifts`);
    - the second Z is tree gluing, giving minimality (876c511de);
    - the Z² carries keyed slots, giving finite type (695a89096).
- **E2 over Z²** (49939b957; referee bh-ref-engines). The minimal crossing-wire fixed-point shift is a free,
  minimal, quantum-rigid Z² SFT. The mechanism is co-location: bits commute once they cross in one tile, and
  frame-forced gadgets are scalars (4f793f5c3).
- **E2 transport.**
  - Centrality (C) passes review for folds, extension localization, and tree-product and Ã₂ transplants
    (cb53a036f), by cylinder transport along forward-determined expansions (5f79e3749, db6f1ea68).
  - Free rigid SFTs over Kazhdan Ã₂ lattices, F_m × F_n and BMW groups are CONDITIONAL on a layout lemma
    (7d228882f).

### What is LEFT for full BH, if E1 and E2 stand

The existence SFT and the rigid SFTs are **different SFTs**. E1's SFT carries the input but is not known to be
rigid. E2's SFTs are rigid but carry no input: they live over Z², lattices, and products of trees.

So, precisely:

**BH ⇐ CARRIER ∧ ( (A₂) for the carrier's SFT  ∨  ( FJ(Λ) ∧ Khanh ) ).**

- **CARRIER (★′):** for every decidable G, an fp Λ ⊇ G carrying one SFT that is minimal, topologically free and
  quantum rigid. This is `decidable-groups-lie-in-fp-groups-with-rigid-topfree-sfts`. For the ring route, add
  torsion-free isotropy; a free SFT has it automatically.
  - This is the only input-dependent statement left.
- **(A₂), group route.**
  - `v-times-subshift-full-group-finiteness-is-horizontal` (89fbf22bb): for V × any topologically free
    subshift, F_n holds iff the domain filtration is essentially (n−1)-connected, which is (A_N). So E3′ = (A₂),
    and nothing about links, packing or heights remains. Rigidity is the linear shadow of (A₂).
  - (A₂) contains P2′b, presentation exactness. That part is input-free and uniform:
    - the gluing kernel is the normal closure of one transposition's defect (95d54d0ca);
    - incomparable lifts are free, so everything reduces to self-swap coherence (CL) (02399e478);
    - over free products, gluing reduces to the local transposition presentation plus EX(Z) (72e3b699d,
      3313c6bb2, 114480fcd);
    - over every fg group, it reduces to FPG plus EX(Z) on the 2ⁿ-letter full shifts over Z, i.e. trivial
      monodromy of τ₀-lifts (96d92cb72, eb337c60f);
    - the smallest case, V_(2,2), is exact (f040a4fa6).
- **Ring route.** Farrell–Jones with coefficients for Λ, plus Khanh (unrefereed) and nothing else: finite
  presentation comes from rigidity by the ring FTR.

**Two meanings of "exactness"** must not be mixed:
- *presentation exactness* is K = 1 for the gluing kernel. It is P2′b: input-free and combinatorial.
- *group exactness* is property A. It is the carrier's wall, below.

### The wall: group exactness

1. **BH forces a finitely presented simple non-exact group.**
   - `decidable-residually-finite-non-exact-group-exists`: Osajda's recursive residually finite non-exact group
     has solvable word problem.
   - `exactness-separates-boone-higman-iff-fp-simple-groups-exact`: if every finitely presented simple group is
     exact, then BH is false.
2. **Every rigidity mechanism found so far produces amenable actions.**
   - This is the open statement **(RA)**, `quantum-rigid-minimal-topfree-subshift-actions-are-amenable`: every
     minimal, topologically free, quantum-rigid subshift action is topologically amenable.
   - Proved pieces (f676c07d2):
     - (RA) holds over F_n;
     - over Λ₀ × F_n, invariant measures live on *tight* points, i.e. points determined by one slab
       Λ₀ × B_R.
   - Compression (boundaries), determinism (Z², crossing wires) and fp-certification (Ã₂) all give amenable
     actions, and every rigidity transport on main preserves amenability.
3. **If (RA) holds, the master route cannot reach non-exact inputs.**
   - No fp overgroup of Osajda's group carries a carrier.
   - By the topologically free necessity theorem, no finitely presented V-stabilized full group of a minimal
     topologically free subshift over a non-exact group exists. This covers every track, including seeds: tree
     gluing turns a rigid seed into a carrier.
   - BH would then need an fp simple non-exact group of an entirely new kind, or be false.
4. **Track B meets the same wall.** Linear gate U is an algebraic uniform Roe embedding, and its C*-shadow is
   Kirchberg, which hosts every exact input and no non-exact one (926454737).

**THE SINGLE DECISIVE STATEMENT: ¬(RA) at Osajda's input.**
> Some finitely presented overgroup of a decidable non-exact group carries a minimal, topologically free,
> quantum-rigid SFT.

- **True:** it is the first non-amenable rigid dynamics, which is the one ingredient the carrier needs beyond
  what exists, and the template for (★′) in general.
- **False,** that is (RA) holds there: the whole master route is confined to exact inputs.

**Where a counterexample can live** (synthesis remark, from f676c07d2).
- Along any free factor, a rigid non-tight point acquires an equivariant end, and that pushes toward amenability.
  So a counterexample must be **tight**: every point determined by one slab, with no free branches.
- The E1 design already has the right slot for this. Λ contains `Z² × (A ∗ Z)` with `A = Λ₁ × Z`, so a slab is
  `Z² × B_R(A ∗ Z)`. The storage column and the keyed-slot planes are exactly where each slab could store the
  whole configuration.
- The design target is a **slab-determined keyed-slot lift**, built from crossing-wire rigid tiles:
  - each Z² plane certifies the A-data around it;
  - (C) holds by cylinder transport, so the base must be readable from the fibre's rule region at every site;
  - no cross-layer separable modifications (db6f1ea68);
  - no antipodal half-space freedoms across layers.

## 1. The complexity face of the carrier: seeds and CAP (v6's gate, now rank 3)

A rigid seed on Λ₀ gives a carrier on Λ₀ ∗ Z (bf61de7d0). So seeds are one road to the carrier. (RA) applies to
them through that gluing, and CAP is their complexity question.

- **Seeds consume decidability exactly.**
  - A recursively presented group with a seed (no rigidity, no density) has solvable word problem (a9187d6d4,
    f06cf5b6f). This is Jeandel localized to the seed cylinder.
  - Rigidity is decided on the derived subshift, since the origin is classical.
  - Seeds never survive marked approximation (c90fc9348).
- **CAP is about the forcing radius.**
  - The sandwich: log T_WP ≲ κ ≲ |Ball(R(n))| · Dehn(O(R(n))) (b970e40ae).
  - Locally finite splittings add one exponential at most, so the locally finite part of 𝒞 is elementary and
    CAP holds there (fed877149).
  - The rungs:
    - BS(1,2) (f6aedfd93) and H₃(Z) (6991cc858) have rigid seeds that certify only their normal forms;
    - Baumslag–Gersten has non-elementary forcing length but a polynomial word problem, so **distortion
      certifies nothing** (17f8da472);
    - one-host compilers are capped at coNP inside nV (5ecd29e1b).
- **Relative seeds glue, and CAP localizes to one HNN extension.**
  - Rigid relative seeds glue along any graph of groups, so every graph of free or free abelian groups with fg
    edge groups is in 𝒞 (5deee0184).
  - A Higman envelope is HNN_s(machine × input), coupled only along graph(F → G) (41501ac60).
  - Higman–Clapham towers leave the seed form at exactly three steps (0d6bf2845):
    - the input as a vertex group, forced by (FA);
    - a rope HNN extension over a regular set;
    - one HNN extension along the halting-set subgroup, which is where CAP lives.
  - **The CAP test:** a rigid relative seed for (K_M, R_0), i.e. a locally forced marking of a hard-membership
    subgroup.
- **Geometry.**
  - The horofunction lemma holds for free and surface groups (9c07701aa), and Roller compactifications of cube
    complexes are SFTs (807e18d5d).
  - But property (T) forbids cube actions. So Kazhdan seeds need non-median Helly systems (horospheres), and a
    tube lemma for hyperbolic groups (1fa63700d).
  - Carving is free: rigidity passes to subshifts. Tree-product lattices are in 𝒞, capped at NP (e3689f09a).

## 2. Gate ranking v7

| Rank | Gate | Lanes |
|---|---|---|
| 1 | **¬(RA) at Osajda's input:** a tight (slab-determined) rigid minimal topologically free carrier; or prove (RA) beyond F_n (first Λ₀ × F_n, then A ∗ Z) | bh-star-a, bh-star-b, new lane |
| 2 | **Carrier for exact inputs:** rigidify the E1 SFT (a crossing-wire keyed-slot lift; (C) by cylinder transport for the A-data layer; single free branch along A ∗ Z) | bh-g1-bss, bh-g1-simulation, bh-g2-fixedpoint-a, bh-free-09 |
| 3 | **CAP at the Higman coupling:** a rigid relative seed for (K_M, R_0) / graph(F → G) | bh-invent-03, bh-invent-14, bh-invent-15, bh-emitter-a |
| 4 | **(A₂) for the carrier's SFT;** uniform P2′b = EX(Z) monodromy + (CL) + FPG | bh-invent-17, bh-p2b-exact, bh-one-relator, bh-invent-16 |
| 5 | **Reviews:** E1 (bh-ref-e1-a/b), crossing-wire rigidity (bh-ref-engines), the 7d228882f layout lemma, Q1.15 (two referees) | referee lanes |
| 6 | **Imports for the ring route:** FJ(Λ) for `((Λ₁×Z)∗Z)×Z²`; Khanh | — |
| 7 | **Q3.4 residue:** after Q5.9 = NO, the BH ⇒ PBH residue is BFFHZ Q3.2 for non-MIF fp simple groups (circle-type); first test T | bh-ffwz-q59 |
| — | Structured lemmas (§3) | MAJOR teams |

## 3. Structured classes

- **Cubulated, BBCMP Q1.15: CLAIMED YES** (877d63985; two referees).
  - The flagged pointed-cube category resynchronizes codings, and its boundary is the whole Roller boundary.
  - With Cuntz packing and free exits, every group acting freely and cocompactly on a CAT(0) cube complex would
    embed in an F_∞ simple group.
  - The pointed-cube + Cuntz route without flags reaches only cubulations whose regular Roller boundary is closed
    (914bce298).
- **Closed MCG, 5.3(2).**
  - Synchronization is proved in every rank by a half-tube shared vertex (e0337551b). So Ore = tree domination
    (141898aff), and least-damage recursions terminate on every test (6449ca40f).
  - Condition (G) reduces to pairs of moves (5a7d8353e, f0d690dc4).
  - Finite presentation of the rational projective full group is OPEN, together with the tracking lemma
    (a65f9528b, e120be82f).
- **H4 / BG, 5.3(9).** G₁ = BS(1,2) ∗_Z BS(1,2) is in B_A (80ce687aa), and so is every finite BS chain
  (23e5c5c7d). What is left for H4 and BG is only the global symmetry (the rotation or the shift).
- **Hyperbolic F_∞** (Zaremsky / BBMZ Q1.2).
  - Cone matching holds off the branch locus (04ac193c1), and configurations are as finite as atoms (af235c6d8).
  - So the gate is a finite decidable no-cycle test (C) plus colour-tameness.
  - Homology will not refute (39148bf5c).
- **GL_n(Q), 5.3(5).**
  - Tree-boundary codings of Q-inputs need fp residually finite semilocal vertex groups. That is the (SL) form of
    the Z_(l) bottleneck, now its fourth consumer (9d121fa9c, 18e02cd45).
  - Independent scalings need commuting colours (e8df48ee6).
- **Solvable.** Hall's group lies in the isolated Abels group A₄/Z, so CGP Question 4 holds for the Hall–Abels
  quotients (d8784610e). A finitary overgroup must be levelled by point stabilizers (399d8c45f, 3bd169bc8).

## 4. Retired in v7, and corrections to v6

- **Track C (stabilizer engines) is dead** (a23f54860, referee PASS).
  - fp engines need fp, isolated, torsion vertex groups, by collapse transfer (58db3f3f9).
  - Engines of non-fp simple groups are not fp.
  - v6's identification (S1) stands as a remark with no route behind it.
- **Reid's group is not finitely presented** (`free-product-emitter-full-groups-need-isolated-vertex-groups`,
  referee PASS). So MO 339541 is answered in full. That is consistent with v6's (S2): the C_Z blow-up is
  Matui-fp.
- **Kernel removal is not a general PBH constructor:** FFWZ Q5.9 is NO, unconditionally (18523f6b4, 9dfa9e546).
- **Distortion as a CAP test** (17f8da472), and locally finite seed towers as CAP candidates (fed877149).
- **Fibre-product closure of rigidity,** and v6/bh-free-09's "common open determinism cone" design rule
  (34f57977b; corrected by db6f1ea68).
- **Effective-residual separators:** P_eff dies in every full host with a reversible universal model
  (49984b668). The live separators are P_Z, (RT) and exactness.
- **Passive enlargements of labelled hosts** (label dichotomy, 25fe3dd25).
- **Homology as a refuter of BBMZ Q1.2** (39148bf5c).
- **Correction: v6's decisive statement, CAP, is demoted to the complexity face.** (RA) covers every master-route
  construction, seeds included, and CAP covers only seeds.
- **Correction: v6's FSG(Z,2) is now EX(Z),** the universal residue of P2′b (96d92cb72).

## 5. Named results since v6 (off-route)

- MO 339541: non-finite presentation, referee PASS.
- FFWZ Q5.9: NO, referee PASS.
- Kourovka 17.61: CT_P(Z) is F_∞, referee PASS (4697bc8f5).
- BFFHZ Q3.1: referee PASS.
- T_{2,3} and T_τ are F_∞ (8c548b3da).
- Kourovka 21.140 is reduced to FP_∞ of the Basilica HNN extension (6dc3f9d10).
- nV inside CT(Z) needs n − 1 odd primes (7a141a647).
- Q1.15: claimed.

## 6. Assessment

**BH true: leaning yes, about 60/40, down from 65/35.**
- **For:** E1 closed and E2 over Z² closed, both pending review. (A₂) is purely horizontal, and P2′b is reduced
  to one monodromy statement.
- **Against:** the carrier now meets one wall, group exactness, which every known rigidity mechanism respects.
  And BH forces a finitely presented simple non-exact group that nobody has seen.
- **The most informative next proof:** decide (RA) at Osajda's input. The constructive side is a tight,
  slab-determined, rigid keyed-slot carrier. The destructive side is extending the end map of f676c07d2 from
  Λ₀ × F_n to Λ₀ × (A ∗ Z).

## 7. Reconciliation log (v7)

- **E1:** 74597e3ce, 876c511de, b0fac81d0, c797680f6, fd33bb9f8.
- **E2:** 49939b957, 4f793f5c3, cb53a036f, 5f79e3749, db6f1ea68, 34f57977b, 7d228882f, 47f947ad2, cc1e8896b,
  4c2d76fe4.
- **(RA):** f676c07d2.
- **E3′ / P2′b:** 89fbf22bb, 95d54d0ca, 02399e478, 72e3b699d, 3313c6bb2, 114480fcd, 96d92cb72, f040a4fa6,
  29b6c4feb.
- **Seeds / CAP:** a9187d6d4, f06cf5b6f, c90fc9348, b970e40ae, fed877149, f6aedfd93, 6991cc858, 17f8da472,
  5deee0184, 41501ac60, 0d6bf2845, 5ecd29e1b, e3689f09a, 9c07701aa, 807e18d5d, 1fa63700d.
- **Engines:** a23f54860, 58db3f3f9.
- **Q3.4:** 18523f6b4, 9dfa9e546, 592de4a85, a5f6a15a5, 556e03d6f.
- **Gate U:** 926454737.
- **Classes:** 877d63985, 914bce298, e0337551b, 141898aff, 6449ca40f, 80ce687aa, 23e5c5c7d, 04ac193c1,
  af235c6d8, 9d121fa9c, d8784610e.
