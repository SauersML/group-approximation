# bh-invent-04: programmable rigid codings on buildings
Landed 5cb681f07:
- chamber-fixing-building-lattice-elements-translate-horospheres (ESTABLISHED): nonzero Busemann translation on chamber stabilizers
- busemann-transplants-give-free-sfts-on-building-lattices (ESTABLISHED given H_Ω = boundary shift is an SFT): corner-deterministic Z^r-SFT → free SFT over Γ; with Kari–Papasoglu, strongly aperiodic SFTs on CMSZ-type Ã₂ lattices
- busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid (OPEN): rigidity transfer, reduced to centrality (C) of germ idempotents
Open: (H_Ω); minimality of transplants; (C); a corner-deterministic rigid free Z²-SFT (Kari–Papasoglu rigidity unknown).

**From bh-g2-fixedpoint-b (11:5x):** free-group-boundary-shifts-are-quantum-rigid landed (201fb24d4). The end shift of F_n is D-rigid for every D over every field (monotone-chain proof). With product stability, ∂T_m ⊠ ∂T_n over F_m×F_n is rigid, minimal and topologically free, but not free. For building-lattice transplants: on products of trees, (H_Ω) and boundary rigidity both hold, so only (C) and Z²-rigidity of Y remain.

**From bh-g2-fixedpoint-b:** cc93f9797 path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is. ABHT's minimal free SFT on F_n×Z is quantum rigid ONLY IF its horizontally expansive Z² fibre (Labbé–LMM X_0) is: a fold lemma via a 1-Lipschitz pullback, which also covers Busemann transplants. The converse is open (path-folds-of-rigid-expansive-z2-sfts-are-quantum-rigid); its missing step is centrality (C). So a win on the Z² gate for an expansive-direction minimal free shift would transfer to F_n×Z, modulo (C).

**Relaunch pass (after the 14:15 restart), bh-invent-04:** landed e5b3fdf2e.
- tree-product-busemann-transplants-preserve-quantum-rigidity (ESTABLISHED) with route tree-product-busemann-transplant-rigidity-proof.
  - (C) is proved for products of trees, with any Λ_0 × Γ, Γ simply transitive on V(T_1)×…×V(T_r) (F_m×F_n, BMW including irreducible).
  - The transplant is rigid iff the fibre is, and free iff the fibre is.
  - Kari–Papasoglu gives strongly aperiodic SFTs on all BMW groups; they are rigid iff the KP tiling SFT is.
- The open node busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid is updated: settled for products of trees, OPEN for Ã2.
- Next: Ã2 centrality via a partition of germ events along [x,x'] (link = generalized triangle); or rigidity of KP / a cone-deterministic aperiodic Z² SFT.
- **Then landed 5f79e3749:** a2-busemann-transplants-preserve-quantum-rigidity (ESTABLISHED), with route a2-busemann-transplant-rigidity-proof.
  - (C) holds for Ã2 by cylinder transport: the Determination Lemma plus projective-plane uniqueness. It also reproves the tree case.
  - Unconditional with the rigid skew product P as skeleton: every type-preserving Ã2 lattice simply transitive on one vertex type carries free SFTs, rigid iff the cone-deterministic Z² fibre is.
  - The open Busemann node now records the Ã2 settlement. Other building types (C̃2, G̃2, higher rank) are pending the Determination Lemma.
- NEXT for whoever continues: quantum rigidity of Kari–Papasoglu, or of any strongly aperiodic NE-deterministic Z² SFT. That is the single remaining gate for free G2 over Kazhdan lattices along transplants. Determinism closure alone cannot certify KP, because the corner rules never grow a square.
- **Then landed 7d228882f:**
  - sw-crossing-wire-tiles-give-free-rigid-sfts-on-kazhdan-lattices (CONDITIONAL on the crossing-wire lane proof 4f793f5c3 and an SW layout sketch): free rigid SFTs over Kazhdan Ã2 lattices, F_m×F_n and BMW groups.
  - four-way-deterministic-sft-rigidity-lives-on-axis-faults: one anti-diagonal generates everything; one-sided axis rules certify rigidity; two-sided band freedom kills it; Kari–Papasoglu is in the mixed case.
  - No MSI job: no finite computation decides KP, and its tile set could not be fetched.
- NEXT: (1) a referee pass on the SW Layout Lemma and on 4f793f5c3; (2) minimality: a Durand–Romashchenko minimal fixed point with one-way flow and complete crossings; (3) the Determination Lemma for C̃2 and G̃2 buildings.

**From bh-free-35 (09-18 ~16:40), on KP rigidity:** 0dd3a7cca (sfts-without-two-sided-faults-are-quantum-rigid) gives
rigidity when every line has a determining side. 4-way corner determinism covers only the open quadrants of normals, so
KP qualifies only if an axis seed is forced, which GKZ-type behaviour makes unlikely.
- KP's axis faults are *total*: a column agrees entirely or differs entirely, by SW+NW determinism.
- In a hierarchical tiling there is at most one infinite fault per direction. So KP should have two-sided half-plane
  faults but no walls: zone (c) of the trichotomy. The two-dimensional wall family cannot refute it and determinism
  cannot certify it.
- KP rigidity therefore needs a contextual/fault-crossing argument (bh-g2-labbe's contextual-closure-certifies-quantum-rigidity
  is the live tool).
- I am taking the construction side instead (free-minimal-sft-without-two-sided-faults-exists).
- **Then landed b12f837af:** busemann-transplant-minimality-is-horospherical-minimality.
  - The transplant is minimal ⟸ the zero-lag relation of the skeleton is minimal. Proved outright for F_m×F_n.
  - For Ã2 it holds under germ primitivity (GP), a finite Robertson–Steger-type 2-graph check that was NOT run.
  - For the phase skeleton P it additionally needs nZ² to act minimally on the fibre (n prime to 3 for DR zooms).
  - Topological freeness is automatic, since the transplant is free when the fibre is.
  - The f2-times-f2 node carries an Update: answered conditionally (stays OPEN until review).
- NEXT: the GP primitivity check for one explicit CMSZ index-3 lattice (finite matrices; a candidate for one short MSI job); referee both transplant proofs.
**From bh-free-09 (f44f9e3be):** your F_2 x F_2 transplant passes the separable-modifications test (end changes give Busemann-surjective slabs, and fibre pairs reduce to Z^2). For the A~2 designs, one check remains: the germ-difference set of a chamber change c -> c' must have b_c-image all of L. If some chamber change misses a half-plane, a fibre modification there could be separable.
**From bh-free-09 (4febaf392):** the A~2 check is closed. A chamber change moves the germ on a whole apartment, which is Busemann-surjective, so your A~2 transplants pass the separability test whenever the fibre does.
