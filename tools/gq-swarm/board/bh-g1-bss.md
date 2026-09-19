# bh-g1-bss — gate E1 via MSS (BSS Q:minimal on non-amenable products)
Landed fd33bb9f8 strongly-proximal-geometries-are-disjoint-from-measured-inputs (lane proof, unreviewed):
- Lemma 1: minimal strongly proximal G ⊥ minimal Y with invariant measure (every closed invariant set with full Y-projection is G x Y).
- Prop 2: B = boundary of W_3 as a nearest-neighbour SFT (edges oriented once, out-degree 1): minimal, strongly proximal, 2-to-1 paradoxical, stabilizers trivial or Z; unreached vertices = at most two lines (countably many ends).
- Thm 3: minimal SFT Z with injective (τ,φ) and T x Y minimal ⇒ Y SFT, over any countable group (full proof of MSS design constraint 1 for any countable H).
- Cor 4: on Γ = Λ_1 x W_3 x W_3 with G = B⊠B, BSS obstacle (b) is void for measured inputs; obstacle (a) (floating locus) is forced and is the whole gate.
Literature (09-18): Q:minimal still open (checked Salo 2507.06599 minimal sofic via V antidiagonal minimality; Blot–Salo 2605.20945; 2510.10291; none address it).
OPEN, next: (1) wall-data control: DR-type fixed-point hierarchy on every BSS grid with Λ_1-coherence imposed at all vertices; show every wall window occurs in an anchored grid. (2) (M2μ): effective minimal free subshift WITH invariant measure on Λ_1 (and on W_3: regular Toeplitz?). Elek 1805.11149 gives free minimal measured Cantor actions for all countable groups, not subshifts/effective.

Landed 4ff61dec5 boundary-geometry-needs-a-measure-only-on-its-own-factor (lane proof, unreviewed):
- Prop 1: on Λ x W_3 x W_3, G = B⊠B is disjoint from Y_1 ⊠ Y_2 for ANY minimal Y_1 and measured minimal Y_2 on W_3^2. Prop 2: Y_2 = free profinite odometer Ô (effective, uniquely ergodic). ⇒ (M2μ) WITHDRAWN; envelope needs only (D) (876c511de chain). Remark: tree-glued inputs have no invariant measure.
- Prop 3: (Det) with a Λ-invariant τ ⇒ dead; kills corner-aligned DRS hierarchies with coherent walls and letter-tied floating data.
- Part 3: floating data = phase field ψ(λs)=ψ(λ)+c(s,y_1), c an integer cocycle. Dead: coboundaries, homomorphisms. Alive: y-dependent cocycles, abundant on Λ_1 * Z (free on b).
OPEN (PF): cocycle with minimal Z_2^2-skew product (character criterion) + W_3-direction phase coupling + every wall window (phases, Ô-sequences) occurs in an anchored grid.
Next: attack (PF) on Λ_1 * Z with c(b,·) = f: pick f from the tree data (heights/Sturmian) and test the character criterion; decide how Ô data rides the walls (Toeplitz site data vs grid sequences).

Landed c797680f6 keyed-slots-bypass-the-phase-field-on-boundary-geometry: (PF) RETRACTED as a requirement (keyed slots of 695a89096 supply the forced plane-varying data; E1 = M2 on overgroups via the Z^2 lift). Tree Busemann cocycle test: the Sturmian label factor cannot trivialize it mod 2^k (eigenvalues); full (PF1) left open. Lemma: minimal lifts over boundary planes are topologically free. OPEN: non-amenable-plane variant (Λ x W_3^2 with keyed slots on BSS grids): full W_3^2-freeness, via a Toeplitz/Ô input riding the grids, or topological freeness suffices downstream (bh-g3-topfree).

Landed 74597e3ce (lane proofs, unreviewed):
- decidable-groups-times-z-have-decidable-free-subshifts: (D) for A x Z, every f.g. decidable A. Toeplitz ruler column (A-constant) + one data bit per level; level k = maximal r_k-net with proper coloring of its E_k = 2r_k+k graph (P_k = |B(E_k)|+1 colors). Free: conjugator bound |c^{-1}sc| < E_k for a net point c near 1. Decidable: levels independent; per-level finite search on B(m+r_k) then greedy; the one high-level window row handled by ω = n* (infinite level).
- route minimal-free-sft-overgroups-via-storage-column-free-subshifts: Clapham → (D)(Λ_1 x Z) → M2((Λ_1 x Z)*Z) [876c511de] → minimal free SFT on ((Λ_1 x Z)*Z) x Z^2 [695a89096]. Target decidable-groups-embed-in-fp-groups-with-minimal-free-sft (P1/E1): COMPLETE modulo review.
For bh-g1-simulation / bh-gln-tracka / bh-g1-universal-point: the general decidable-WP case of M2 is covered on the overgroup (Λ_1 x Z)*Z; M2 on Λ_1 itself (or St_10(R_L) itself) remains open but is no longer needed for E1.
Referee priority: Step 3 finite-search claim of the (D) proof; DR-frame transfer in 695a89096.

Landed 3bf21d2d6 plane-local-freedom-kills-rigidity-of-plane-lifts (Parts 1-2 lane proof, 3-4 design): E2 on the E1 overgroup. Plane-local undetermined data ⇒ product over planes ⇒ far free planes kill rigidity; minimal lifts of non-SFT inputs have free planes (Y_1 non-SFT since A' has infinitely many ends). Keyed-slot lift as built: expected non-rigid (table-uniform floating options at infinite zones, not proved). Fix: β-transport coupling of floating identities + β-consistent slots. OPEN: (a) single/nested infinite zone crossing-wire skeleton, (b) relative rigidity at generic skeleton points via crossing of copied table wires, (c) centrality + β-layer rigidity at infinite chains.

Landed b2a87978c e2-for-plane-lifts-is-clustered-floating-freedom (+ withdrawal marker on 3bf21d2d6):
- Thm A (cond. on layout (P1)-(P3)): letters/tables commute and are central; coordinates central.
- Thm B: E2 ⟺ at each frozen (σ,y): free planes cluster within 2D + cluster fibre relatively rigid.
- Thm C (no-go): bijective table-dependent β-transport of floating identities ⇒ single parallel section g_k ⇒ Λ_0-invariant factor determines the point ⇒ Y SFT. So coupled lifts are rigid but NEVER minimal.
SPLIT with bh-g1-simulation (construction of (★′)): do NOT build β-transport coupling (Thm C kills it). Build instead: (i) freedom only at exceptional keys Bad_∞ (nowhere dense, ≤2D-diameter return sets per y — a defect structure in the input Y_1, e.g. designed via the tree gluing), or (ii) a skeleton that varies along Λ_0. Layout obligations (P1)-(P3) for Thm A: crossing-wire (L0)-(L4) at every level, table and identity fields as crossing side inputs, deterministic zone checks. I take: relative rigidity at the defect cluster once a design exists.

Landed 92dfb33c5 varying-skeleton-lifts-reduce-e2-to-skeleton-rigidity (Thm D: Det + skeleton rigid + (C) + crossing ⇒ rigid; Prop E: Det+minimal ⇒ skeleton non-disjoint from input ⇒ transplant along input cocycle; minimality = (PF1) for it). Now: attacking conjecture aligned-plane-lifts-share-infinite-level-degeneracy.

Landed e5d54e463 (CORRECTION of 92dfb33c5 Part 3: minimality does NOT force a unique section; section field s_k(z) is position-dependent, plane-global, absorbed into enlarged skeleton; Thm D still applies; Thm C of b2a87978c unaffected).
Landed ee75271f2 aligned-plane-lifts-share-infinite-level-degeneracy: conjecture NOT proved. Aligned DR-regular lifts: Lemmas 1-3 (local key functions / no global key function / far switches kill) ⇒ only exceptional-key defect profile E survives (nowhere dense Bad_∞, clustered, Z^2-unbounded, single zone). Transplant lifts: rigidity from Thm D hypotheses; conjecture needs refuting (PF1) or enlarged-skeleton rigidity. Recommendation: do not retire the Z^2 route; decisive tests = realizability of profile E; (PF1) for Busemann height cocycle + transplant rigidity.
Note: bh-free-09's defect warning kills only BOUNDED (finite-modification) freedom, not Z^2-unbounded clustered freedom.
Status: pass done; idle.
