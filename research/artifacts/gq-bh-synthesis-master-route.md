# Boone–Higman: master route (synthesis v6, 2026-09-18)

Lead synthesis of the 09-18 BH swarm, lane `bh-synth-lead`.
- **Versions:** v1 12a123bf1, v2 b344473a1, v3 8d0279a62, v4 fa0efca1c, v5 16bd19b7f (Perron rows corrected
  by 85b04172c).
- **What v6 folds in:** every landing and LESSONS.md entry from 14:36 to 16:02 (§7).
- **Status:** this is a strategy document, not a proof. Cited nodes are mostly unreviewed lane proofs, and their
  status lines govern. Items marked **(synthesis remark)** are my own short arguments. They are not nodes and
  are unreviewed. The live table is `board/SYNTHESIS.md`.

## 0. Thesis (v6): one object, the seed

Several independent lanes converged on one object.
- bh-g2-buildings calls it an *SFT compactification* (bf61de7d0).
- bh-invent-13 calls it a *finite-type S-compactification* (6a462d596).
- Lanes bh-emitter-a and bh-emitter-b, and the E1 lanes, reach it from the other side.

**Definition (seed SFT).** Let Γ be finitely generated. A *seed SFT* over Γ is an SFT `Y ⊆ A^Γ` with a point
`y_*` such that:
- (S1) `y_*` is isolated in `Y`, i.e. some pattern π on a ball (the *seed*) has cylinder `{y_*}`;
- (S2) `Stab(y_*) = 1`;
- (S3) `Γ·y_*` is dense in `Y`.

Then `Γ·y_*` is an open, dense, discrete copy of Γ, and `∂Y = Y ∖ Γ·y_*` is the boundary.
- This is exactly (C1)+(C2) of `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`.
- It is also exactly "K of finite type" in part 3 of `stabilizer-engines-embed-in-every-branch-compactification`.
- So **(IE′)(S) and "S has an SFT compactification" are the same statement** (synthesis remark; the definitions
  coincide word for word once "isolated" is read as "Sx open").
- 𝒞 is the class of groups with a seed SFT that is D-quantum rigid over every field for all large D.
  - Known members: finite groups and Z (via `C_Z`, the SFT `…++*−−…` together with its two limit points `±∞`).
  - 𝒞 is closed under × and ∗, which gives Z² and F_n.

**THE UNIFIED GATE (SEED).** For every finitely generated `G` with solvable word problem there are:
- a finitely presented `Λ₀ ⊇ G`;
- a seed SFT `(Y, y_*)` over `Λ₀` that is quantum rigid, i.e. `Λ₀ ∈ 𝒞`.

This is `decidable-groups-embed-in-rigid-sft-compactification-groups`, premise (★𝒞). For the ring route, add:
- (S5) every finite subgroup of `Λ₀` acts freely on `∂Y`.

**Why this is the right object.** Each clause answers a v5 lesson.
1. **It is compression on the input's own points.**
   - Rigidity comes from monotone chains toward the seed, as in `C_Z` and the end shift. So it is cheap,
     compression-type rigidity.
   - But the seed orbit *is* `Λ₀`, so no commuting factor is involved. The attractor lemma
     (`attracting-boundary-factors-fix-commuting-actions`, 377ea1e4d) named "type (A) on the input's own
     points" as the only exit from geometric routes. A seed is that exit made finite-type.
2. **Complexity sits in the groupoid.**
   - `outer-extensions-of-fp-steinberg-groupoids-need-no-rigidity` (2e7954761) says rigidity and the carrier
     principle are one gate: a rigid cheap groupoid plus a complex acting group cannot work.
   - A seed over `Λ₀` carries `WP(Λ₀)` in its own language. By (S3) every pattern of `Y` occurs in `y_*`, and
     `y_*` is computable from `WP(Λ₀)`.
3. **Minimality and freeness come free.** Tree gluing with `C_Z` over `Λ₀ ∗ Z` produces a minimal,
   topologically free, rigid SFT (bf61de7d0 parts 1–3). So the minimality gap of E1 does not arise, and no
   free layer is needed (`free-rewritable-tape-layers-kill-finite-presentation`, 7ac816a5c).
4. **It is what emitters lack.** The one-point compactification `S⁺` is never of finite type, and a seed is
   the finite-type repair (6a462d596 part 3).
5. **It is a groupoid-level object.** Finite presentation of the Steinberg algebra is a Kakutani invariant
   (`steinberg-fp-is-a-kakutani-invariant`). So seeds may be built and checked on any Kakutani model.

**Implications.** "Free form" means the E1/E3 premises for *free* SFTs. "Topologically free form" means E1′/E3′.

| From | Gives | Source |
|---|---|---|
| seed(Λ₀) | E1′ on `Λ₀ ∗ Z`: a minimal topologically free SFT | bf61de7d0 parts 1–2 (rigidity not used) |
| rigid seed(Λ₀) = `Λ₀ ∈ 𝒞` | E1′ + E2 on `Λ₀ ∗ Z`: (★′) in group form | bf61de7d0 part 3 |
| `Λ₀ ∈ 𝒞` with (S5) | (★′) with torsion-free isotropy on `Λ₀ ∗ Z` | isotropy of the glued SFT: ends ≤ Z, sink pieces = `Stab_{Λ₀}(ξ)`, ξ ∈ ∂Y |
| seed(Λ₀), `WP(Λ₀)` solvable | (D′): a topologically free SFT on `Λ₀` with decidable language | synthesis remark (below) |
| (D)(A): a free subshift with decidable language | (M2) on `A ∗ Z` (free form) | 876c511de |
| (D)(Λ₁) ∧ MSS | E1 on `(Λ₁ ∗ Z)²` (free form) | 876c511de route |
| (M2μ)(Λ₁) ∧ floating-locus control | E1 on `Λ₁ × W₃ × W₃` (free form) | fd33bb9f8 |
| (IE′)(S) = seed(S) | the blow-up engine `F_S^Y` has finite type, and equals the full group of the glued SFT over `Z/2 ∗ S` | 6a462d596; identification (S1) below |

**Non-implications.**
- A seed SFT over an infinite group is never shown to be free. `C_Z` has fixed points at `±∞`, and every
  nonempty Z-SFT has periodic points, which lie in ∂Y. So seed ⇏ (D).
- A seed carries no invariant probability measure on its discrete orbit. So seed is unrelated to (M2μ).
- (D) ⇏ seed, since (D) asks for no isolated point and no finite type.
- **Where this leaves (D), (M2) and (M2μ).** They are premises of the *free* form. The free form's finiteness
  step needs an infinite-type theorem (`free-sft-hosts-admit-no-finite-type-coding`, 00a44f5d54). On the
  primary, topologically free route the seed supersedes them: it gives E1′ as an SFT outright.

**Synthesis remark (D′).** Let `Λ₀` have solvable word problem and a seed SFT.
- By compactness, for each n there is an m such that exactly one B_n-pattern extends the seed to a locally
  admissible B_m-pattern. Searching over m is effective, so `y_*` is computable.
- By (S3), the language of `Y` is the set of patterns of `y_*`, which is c.e.
- Non-occurrence is c.e. by compactness.
- So the language is decidable.

**Synthesis remark (S1): Track C is the glued seed over Z/2 ∗ S.**
- Glue a seed `Y` over S with the finite-group seed of `Z/2`, as in bf61de7d0. That finite seed has empty
  boundary.
- By Step A there, the points of the glued SFT are the ends of the Bass–Serre tree, together with one sink
  S-piece carrying a configuration in ∂Y. As a D-set, that is exactly `Ω^Y = ∂T ⊔ ⊔_v ∂_v` of 6a462d596.
- So the finite-type engine `F_S^Y` is the full group of the glued seed SFT over `D = Z/2 ∗ S`. The topology
  should agree, since both spaces are compact; one lane check is still needed.
- **Tracks A′ and C are therefore one construction:** a glued seed over `Λ₀ ∗ H`. They differ only in:
  - `H = Z` versus `H = Z/2`;
  - with or without V;
  - whether the vertex group is an fp overgroup or the simple input.
  S ≤ D(F) uses only that S is perfect.

**Synthesis remark (S2): the bottom rung is already finitely presented.**
- Take S = Z and `K = C_Z`, the two-point compactification.
- `Ω^K` is the end space of the Cayley tree of `Z/2 ∗ Z` in the standard generators. A ray either stays in
  one t-line, giving `±∞_v`, or crosses infinitely many a-edges, giving an end of the Bass–Serre tree.
- `v-times-tree-boundary-full-groups-are-f-infinity` item 1 makes `(Z/2 ∗ Z) ⋉ ∂T` Matui's `G_A`, with A
  irreducible and not a permutation matrix.
- So the first blow-up `F_Z^±` of Reid's group is finitely presented, by Matui's theorem for one-sided SFT
  groupoids (recalled, not re-read), and `F_Z ↪ F_Z^±`.
- **Consequence.** The finite-type obstruction at an emitter is an artifact of the one-point compactification, and Reid's group is only the
  bottom test.

**Routes and conditional theorems v6.**
- **R1 (ring).** BH ⇐ (SEED) ∧ (S5) ∧ (K′: Farrell–Jones for `Λ₀ ∗ Z` with coefficients) ∧ Khanh.
  - It runs through `rigid-topfree-sfts-via-rigid-sft-compactifications` and
    `boone-higman-via-leavitt-units-of-rigid-topologically-free-sfts`.
  - No P2′ is needed. Finite presentation comes from rigidity by the ring FTR, so no finite-state cap applies.
- **R2 (group).** BH and PBH ⇐ (SEED) ∧ E3′ for the glued SFT.
  - E3′ ⇐ P2′a (topologically free form) ∧ FSG(F_n, A), by `gluing-kernels-descend-from-the-full-shift`
    item 6 and `gluing-kernels-descend-from-the-free-group-full-shift`.
  - R2 needs neither Farrell–Jones nor Khanh.
- **Only (SEED) depends on the input on either route.**

## 1. The gates (v6)

### Gate 1, (SEED): the decisive gate

**The decisive next statement is ¬CAP.**
> **(CAP)** There is a fixed complexity class (say EXP) containing the word problem of every finitely presented
> group in 𝒞.

- *CAP ⇒ ¬(SEED).* Take a decidable G whose word problem is not in the class. Any fp `Λ₀ ⊇ G` has a word problem
  at least as hard.
- *So CAP true* kills R1, R2 and Track C at once. By the one-gate lesson (2e7954761), it would also block every
  SFT-coordinate host.
- *CAP false* gives one fp group of large complexity with a rigid seed. What remains after that is uniformity:
  every decidable G.
- *Why CAP is not decided by what is known.*
  - Finite-state Li codings cap at `2^{Cl²}` (`finite-state-li-coded-full-groups-have-exponential-word-problem`).
    But a seed need not be finite-state.
  - The algorithm computing `y_*` searches to an extension radius m(n) that can be arbitrary.
  - The two recorded rigid instances (trees, Ã₂) are finite-state (2914b739e). That is exactly why they carry
    nothing hard.

**Constructive attack: closure of 𝒞 under HNN extensions and amalgams along seed-coded associated subgroups.**
- *Why HNN extensions.*
  - 𝒞 is closed under × and ∗, but those operations never carry inputs: a simple group in A × B lies in a factor,
    and an (FA) group in A ∗ B lies in a conjugate of a factor.
  - Higman–Clapham-type embeddings, which put a decidable group into an fp decidable group, are built from
    HNN extensions and amalgams over finitely generated associated subgroups (recalled).
- *Why "seed-coded" is the right hypothesis* (synthesis remark). Suppose an associated subgroup's cosets are
  marked by a deterministic layer over the seed. Then membership in it is read off the computable `y_*`, so it is
  decidable. That is exactly the condition under which HNN extensions keep the word problem solvable, so the
  hypothesis consumes decidability where Clapham consumes it.
- *The rungs.*
  - **(1a) BS(1,2) = Z ∗_{a↦a²}.** A seed is plausibly a sink-oriented Bass–Serre tree, with `C_Z` on the sink
    vertex's a-line and a deterministic parity layer. Existence and rigidity are both unchecked. This is the
    first HNN extension over a distorted edge.
  - **(1b) H₃(Z) = Z² ⋊ Z.** The product seed on Z² is not shear-invariant: the central coordinate moves without
    bound (bf61de7d0 test list). So this rung tests the compatibility hypothesis itself.
  - **(1c) An HNN tower that simulates a machine** (a Sapir–Birget–Rips type group). This is the first real test
    of CAP.
- *Irreducible geometry.* Input groups with (FA), such as `H_Γ`, lie in a conjugate of a vertex group of any
  splitting. So gluing cannot supply their geometry.
  - Some seed must code a one-ended geometry with property (FA) directly: the Kazhdan filter, 813bff6dd, says
    Y must code the input's geometry.
  - **(1d) A rigid seed over a cocompact Ã₂ lattice.** Such a lattice acts simply transitively on vertices, so the
    candidate is a locally checkable vector-distance field to one vertex. Its boundary shifts are already rigid
    (9b3fdd027).
  - A positive answer is the first seed over a Kazhdan group.
- **Lanes:** bh-g2-buildings (closure, test list), bh-invent-13 / bh-emitter-a / bh-emitter-b (seed side of
  emitters), plus new lanes for 1a–1d. (D) and (M2μ) (bh-g1-universal-point, bh-g1-bss) stay as free-form
  premises.

### Gate 2, finiteness on the group route (R2 only): P2′a and FSG

- **P2′a.** For a rigid topologically free SFT X over an fp Λ, is `N_X = LC(X,V) ⋊ Λ` finitely presented?
  - The node on main is stated for free SFTs (`rigid-sfts-give-fp-v-boolean-power-crossed-products`, OPEN). It is
    reduced to far-site conditioning (bh-free-29), with cone sliding (3f547b04c) as the tool.
  - **Correction to v5:** v5 said "P2′a is supplied by (★′)". That was too strong; P2′a is OPEN.
- **P2′b = FSG.**
  - For topologically free X, P2′b(X) is finite presentation of `F(T_X)` relative to `N_X`, which is necessary
    for finite presentation (7054f9da2 item 6).
  - The full shift is the universal case (a3332a1c4).
  - Along quotients of the acting group, the universal case is **FSG(F_n, A)** (eb337c60f). It gives P2′b for
    every subshift over every n-generated group, with no freeness needed.
- **Decision on FSG(Z,2): not the decisive statement; kept as the top test of Gate 2.**
  - *Refutations climb.* Z is a quotient of every F_n (n ≥ 1). By eb337c60f items 1–3, FSG(F_n, 2) ⇒ FSG(Z, 2),
    and 2^{F_n} ⊆ A^{F_n} gives FSG(F_n, A) ⇒ FSG(F_n, 2). So **¬FSG(Z,2) ⇒ ¬FSG(F_n, A) for all n ≥ 1 and
    |A| ≥ 2.** A no kills the uniform, dynamics-free P2′b programme, and R2 would then have to prove exactness
    for each X separately.
  - *Proofs do not climb.* A yes is only the rank-one base case, and F_n with n ≥ 2 adds branching in the label
    group.
  - *Why it is not the decisive statement.* FSG is off route R1 entirely. It is not input-dependent. And E3′
    already holds on the recorded instances by Li's theory.
  - *Why it is still the right first test.* `F(T_{2^Z})` embeds in 3V via the baker's map (bh-p2b-exact). So
    FSG(Z,2) asks whether this subgroup of 3V is finitely presented relative to `LC(2^Z,V) ⋊ Z`. A Quick-type
    local transposition presentation (0326d0d8a) is the natural attack, and conjugacy with overlapping supports
    is the open part.
- **Lanes:** bh-p2b-exact, bh-one-relator (FSG); bh-g3-tfc, bh-free-29 (P2′a).

### Gate 3, programmable rigidity: the calibration for (SEED) over hard groups

- **All of G2 in layered designs is centrality (C)** (4a734659e).
  - Tree folds are rigidity-neutral: (C) is proved for the ABHT fold, so its F_n × Z SFT is rigid iff its Z²
    fibre is (3c8b41742).
  - So folds, products with boundary shifts, and automorphic extensions add no rigidity.
- **Rigidity is a finite test for self-similar tile sets.**
  - For fixed-point tile sets it is a bounded-range test, semi-decidable with a finite certificate (9c360c2ca).
  - Thin walls refute it at every scale. The design rule is one-sided determining columns and no
    information-free macrotile column.
- **Labbé's shift is decided at scale 2**, by the 229 legal 5×5 patterns (1bf712168). That finite computation is
  running on MSI (bh-g2-labbe).
- **Why it matters for (SEED).**
  - A seed over a hard-WP group must be non-finite-state, so its rigidity will be the rigidity of a hierarchy.
  - DRS fixed-point tile sets are the only programmable hierarchies with a finite rigidity test.
  - The first rigid fixed-point tile set is therefore the template for rung 1c.
- **Lanes:** bh-g2-labbe, bh-free-35, bh-g2-fixedpoint-a, bh-free-09.

### Gates 4–7

- **4. Track C residue.** Can `D(F_S^K)` be finitely presented over a non-fp vertex group?
  - bh-emitter-b's candidate says an fp engine forces an fp vertex group. That would make the simple-S version
    circular, and Track C would merge fully into R2 with an fp perfect vertex group.
  - Reid's group (MO 339541) stays a named question. It is no longer a gate, by (S2).
- **5. Q3.4 = kernel removal** (FFWZ Q5.9; bh-ffwz-q59).
  - Every move language is a full group in disguise (4060cc1fc). So operadic, Thompson-like and groupoid hosts
    certify exactly B_A and never separate BH from PBH.
  - Operads beat SV_G only through unbounded refinement depth.
- **6. Imports.** (K′), Farrell–Jones for `Λ₀ ∗ Z`, is needed on R1 only. Khanh (arXiv:2609.08428, unrefereed) is
  also needed on R1 only.
- **7. Gate U (Track B) is linear and merges into (SEED).**
  - Non-amenable scaffolds absorb the Leavitt factor, and the Kazhdan, ends and separation caps apply to
    permutation matrices only (04323a8af). So gate U is posed linearly over one fixed non-amenable FJ scaffold.
  - Its oracle language must then be carried by a rigid SFT groupoid (2e7954761 ceiling). That is the seed gate
    again.
  - Automorphisms do not help: they are outer over ICC scaffolds (9823dcde1).

## 2. Structured classes (MAJOR teams): one lemma each

- **Closed MCG (5.3(2)).** Synchronization in every rank reduces to shared rays at totally irrational directions
  (abd02ad86). It is free at very well approximable directions, so the gate sits at Dirichlet-scale directions.
  Ore for 𝒪_E is LD_atom alone in every rank. Lanes: bh-major-mcg-2, bh-free-54, bh-free-61.
- **Cubulated (Q1.15).**
  - **Correction to v5:** the Perron criterion is refuted (ba9176b48a). Li needs merge packing, which fails
    exactly along thin cycles (63bf7063b).
  - Cuntz stabilization gives packing for free: every Li-Garside full group with trivial units and (Acyc) is F_∞
    after stabilization (16be960ff).
  - Q1.15 is now purely dynamical: (G1) a closed bisection set, (G2) (Acyc), (G3) comparison or minimality.
    Lane: bh-major-cube-b.
- **One-relator / H4 / BG (5.3(9)).**
  - Rank is a spectrum budget. A BS chain needs dilation rates 2^(2^n), so hosts need infinite Hirsch length
    (f0eb931cd). PL germ towers are never faithful, and ascending germ towers give F_∞ extensions (398b7ad02).
  - The target is non-ascending germ towers with fp SingFix groups. This is also rung 1a–1b territory for (SEED).
- **GL_n(Q) (5.3(5)).**
  - The primes must ride on the acting group or across coordinates:
    - one-coordinate registers admit no dilation in nV, SV_G or 2V_τ (1d38dc7fd);
    - single-radix coordinates are dead for `Q ⋊ ⟨d⟩` (541875e2c);
    - monomial Leavitt units are never self-doubling (a89211082).
  - The St₁₀(R_L) embedding half is kernel-checked in Lean (a7d68b30b). In seed terms, 5.3(5) is (SEED) for an
    fp overgroup of St₁₀(R_L). Lanes: bh-gln-centralizer, bh-free-16.
- **Product closure / JE.** The whole recorded fp simple census lies in B_A (2d9a15b01, 6b0d24a14). PBH is
  finite presentation of the host on both machines. So a JE, (SQ) or Q3.4 counterexample must be built by
  neither full groups nor Leavitt-tensor units.
- **Kourovka / MO, named, off-route.** Referee PASS: 21.74(b),(c) and 21.75 (fac0259d6); 17.57, second pass
  (de5229224); MO 339541 abelianization (6a0a3642f). Also: Conway's amusical permutation is the full 3-shift
  inside CT(Z) (b8fa45c9d).

## 3. Gate ranking v6 (decisiveness × tractability)

| Rank | Gate | Lanes |
|---|---|---|
| 1 | **(SEED) via ¬CAP:** HNN/amalgam closure of 𝒞 along seed-coded subgroups; rungs 1a BS(1,2), 1b H₃(Z), 1c a machine-simulating HNN tower | bh-g2-buildings, new lanes |
| 2 | **(SEED), irreducible geometry:** a rigid seed over a cocompact Ã₂ lattice (rung 1d) | bh-invent-13, bh-emitter-a/b, new lane |
| 3 | **FSG(Z,2)** (rank-one test of FSG(F_n,A); a no climbs to all F_n), then FSG(F_2,A); **P2′a** (topologically free form) | bh-p2b-exact, bh-one-relator, bh-free-29, bh-g3-tfc |
| 4 | **Programmable rigidity:** Labbé J₂ = 0 (MSI, running); a DRS certificate; (C) for fibre products | bh-g2-labbe, bh-free-35, bh-g2-fixedpoint-a, bh-free-09 |
| 5 | **Track C residue:** fp engines over non-fp vertex groups | bh-emitter-b, bh-free-60 |
| 6 | **Q3.4 / FFWZ Q5.9** | bh-ffwz-q59, bh-typeA-universal |
| 7 | **Imports (K′), Khanh** (R1 only) | — |
| — | Structured lemmas (§2) | MAJOR teams |

**Retired in v6:**
- **The free form as the primary route.** No finite-type coding exists (00a44f5d54). (D), (M2), (M2μ) and MSS
  remain free-form premises only.
- **Reid's group as the top gate.** The emitter is only the bottom of the blow-up lattice, and the next rung is
  Matui-fp (S2).
- **Rigidity from a fixed compressive factor:** folds (3c8b41742), boundary products and time lifts (377ea1e4d),
  automorphic extensions (2e7954761), and Aut or RCA hosts (9823dcde1).
- **Minimality from noise, tape or surgery** (7ac816a5c).
- **For GL_n(Q):** single-radix and one-coordinate registers of Q; monomial self-doubling units.
- **Finite-Hirsch-length and cheap zoom-tower hosts** for BS chains.
- **Gate-U caps as universal obstructions.** They are permutational only.
- **Perron finiteness** (v5 error).

## 4. Corrections to v5

1. "A negative Reid answer kills the whole engine family" was wrong. It kills only the bottom member (6a462d596),
   and the next member is already fp (S2).
2. "P2′a is supplied by (★′)" was too strong. P2′a is OPEN.
3. The Perron criterion was cited as a success. It is refuted (ba9176b48a, corrected on main by 85b04172c).

## 5. Reconciliation log (v6)

- **Seed convergence:** bf61de7d0, 6a462d596, 876c511de, fd33bb9f8, 2e7954761.
- **Topologically free Track A:** 2914b739e.
- **Rigidity:** 3c8b41742, 4a734659e, 9c360c2ca, 1bf712168.
- **Kills:** 00a44f5d54, 377ea1e4d, 7ac816a5c, 9823dcde1.
- **P2′b:** 7054f9da2, a3332a1c4, eb337c60f.
- **Gate U:** 04323a8af.
- **Q3.4 and census:** 4060cc1fc, 2d9a15b01, 6b0d24a14.
- **Chains:** 398b7ad02, f0eb931cd.
- **GL_n(Q):** 541875e2c, 1d38dc7fd, a89211082, a7d68b30b.
- **MCG:** abd02ad86.
- **Cubes:** ba9176b48a, 63bf7063b, 16be960ff.
- **Named problems:** fac0259d6, de5229224, 6a0a3642f, b8fa45c9d.
- **Summary:** c7f12fba7.

## 6. Assessment

**BH true: leaning yes, about 65/35.** The number is unchanged, but the risk is now one question: can a locally
checkable, quantum-rigid coordinate system with a unique origin carry an arbitrary decidable word problem?
- **For:**
  - The lanes converged on one object from four directions.
  - Each route needs nothing else input-dependent.
  - The bottom emitter rung is already fp, and every recorded fp simple group is in B_A.
- **Against:**
  - Every recorded rigid seed or compression coding is finite-state (trees, Ã₂, products).
  - (FA) inputs cannot be glued in, so some seed must code one-ended Kazhdan geometry directly.
- **Most informative next proof:** decide CAP on its first rungs. The cheapest is a rigid seed on BS(1,2) (an HNN
  extension over a distorted edge), then H₃(Z), then a machine-simulating HNN tower.
