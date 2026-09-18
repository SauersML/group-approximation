# bh-free-55 (free lane; seed: Lagrangian Thompson group for Deligne's lattice)
**Approach:** groupoid hosts on Cantorized flag varieties. Signature: "unimodular Maslov cells × Cuntz". First falsifiable step, now done: do the signature cells of unimodular symplectic frames separate points of Λ_n(R)? Yes: a Levi move plus an integral translation, via the Schur complement.
**Landed:**
- aaef738bb
  - `unimodular-maslov-cantorization-is-minimal-expansive` and its proof route. It is ESTABLISHED: Y_u is Cantor and π: Y_u → Λ is onto (injective over Λ^0). The Sp_2n(Z)-action is expansive (one-frame generating partition), minimal (parabolic contraction, no citation) and topologically free mod ±I, and its clopen algebra is decidable (Tarski). Minimality and topological freeness transfer to bh-free-14's Y_Λ.
  - `deligne-lattice-in-fg-simple-lagrangian-brin-thompson-group` and its proof route. It is ESTABLISHED for every n ≥ 2, n = 2 included (the F_3^{2n}∖0 factor handles the central involution). D(2V_Λ(n)), with 2V_Λ(n) = [[𝒢_n × G_2]], is simple, f.g. and has solvable WP, and it contains Deligne's lattice. The centre acts through V; the finite abelianization from (T) gives a diagonal trick that lands the lattice in D. At n = 1 the host is 2V and the lattice is B_3.
  - `lagrangian-brin-thompson-group-is-finitely-presented`: OPEN. It includes a concrete first test, the dissection of the mixed atom (1,1,0) of the unimodular triangle at n = 2.
  - Route `deligne-lattice-bh-via-lagrangian-brin-thompson-group` to `deligne-lattice-satisfies-boone-higman`. It is conditional on finite presentation only.
- bc663eae9: Attempts entries on `deligne-lattice-satisfies-boone-higman` and on bh-free-14's `lagrangian-thompson-group-is-finitely-presented` (item 4).
**For bh-free-14 / successors:**
- The odometer is not needed; any infinite-order t ∈ V works.
- For your V_Λ^τ: D is simple if O_τ is minimal, effective and purely infinite, and D contains Γ̃ by the same diagonal trick.
- Finite generation of D(V_Λ^τ) needs expansivity of Y_Λ, which is unknown. Y_u has it.
- f15e782ba: `unimodular-maslov-cells-do-not-dissect-mixed-atoms` (ESTABLISHED, n = 2). The mixed atom (1,1,0) of the unimodular triangle is no finite union of cells: the rank-one slices of Σ(G) force a {G, L_e}-walled cell, and none of those lies in the atom. So Farey-style cell diagrams fail.
**Dead:** "cell-pair diagrams" (the tree-pair analogue with single unimodular cells as pieces) at n = 2.
**Needs:** finite presentation of D(2V_Λ(n)), even for n = 2. Basic pieces must be atoms of arrangements, or the dyadic factor must absorb them.
**Sparks:**
- Stein–Farley complex of "Maslov × dyadic" brick decompositions with GL_n(Z)-type stabilizers.
- AH conjecture for 𝒢_n × G_2 (H_* = 0 by Künneth) would make 2V_Λ(n) itself simple.

- (bh-free-54, 11:19) FYI for 2V_Λ: GL_3(Z) acts on the rational Cantorization of S^2 with every transvection a single edge-split caret (0b16dec6e). If your 2V_Λ has a lattice-type expansion structure (intersections of pieces are unions of pieces, like dyadic bricks), it could be the positive monoid that edge-split-operad-satisfies-ore is missing.
**Pass 2 (coordinator: f.p. + INSIGHT FIRST), landed f86da7972:**
- `cuntz-stabilized-minimal-full-groups-are-acyclic-and-simple` (ESTABLISHED, Li Cor D read at source): 2V_Λ(n) = D and it is simple and acyclic; the same holds for 𝒯_m × Cuntz and for every minimal topologically free action × Cuntz.
- `deligne-class-dies-over-flag-varieties-iff-flag-has-lagrangian` (ESTABLISHED): the lift exists over Sp_2n(R)/P_I iff n ∈ I, and never when there is an invariant measure (so never for W-type models).
- `maslov-cantorizations-have-no-finite-dissection-type` plus proof (ESTABLISHED, n = 2): no Sp_4(Z)-invariant Maslov algebra has FDT, because of corners over Q(√2p); Γ-rigid pair diagrams would force FDT.
**Dead:** Stein–Farley over generalized Γ-rigid pieces for 2V_Λ(2). Li's Garside engine with Γ-rigid tiles is dead too.
**Needs:** a non-algebraic Γ-equivariant recoordinatization of Λ with rational corners (a "Lagrangian ?-function"), or a piecewise-linear Sp_2n(Z) action on Ŝ_m that kills the class (bh-free-14's open node; FDT holds there).
Status: finished (f.p. not proved; standard engine excluded at n = 2).
- 09-18 from bh-typeA-universal (tool you may need): `interval-spherical-brown-criterion` (2923ced58, referee-c PASS on earlier version). Finite presentation of a group acting on a simply connected union Y of finite poset intervals follows from: fp vertex stabilizers, f.g. COVER stabilizers (covers of ANY rank jump, e.g. prime dissections), finitely many orbits of vertices, covers, and non-cover intervals with DISCONNECTED open part. No lcms, joins or grading assumed. For dissection posets with finitely many k-piece dissections, all orbit conditions are automatic on a bounded-rank sublevel, so fp reduces to simple connectivity of that sublevel (directedness + descending links). Intervals with connected open part impose nothing.
