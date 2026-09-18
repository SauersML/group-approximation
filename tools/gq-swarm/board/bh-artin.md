# bh-artin (BH swarm, Artin groups; free mode)
**Direction:** invent devices for 2-connected odd-labelled Artin graphs.
**Landed (lane proofs, not reviewed):**
- 4e7687670: artin-ordinary-foldings-are-retractions; artin-pbh-reduces-along-folding-separators (blocks / folding separations); forest-artin-groups-satisfy-permutational-boone-higman.
- 6e504ecc5: artin-hub-cones-reduce-pbh-to-coned-cliques (NEW DEVICE: add hub e with labels k_v | every incident label; A_Γ is a standard parabolic of the cone, whose vertex stars are foldable separators; reduces B_A to coned maximal cliques); triangle-free-all-3-artin-groups-satisfy-pbh (every triangle-free all-3 Artin group, e.g. the all-3 four-cycle (not virtually cocompactly cubulated, HJP), is in B_A via Ã_2 pieces). Root + folding-node Scope updated.
**Open / next:** vertices with coprime incident labels (e.g. 4-cycle labels 3,3,3,2 — single odd component, no hub labelling, no foldable separator); complete pieces (K_4 all-3 = ideal regular tetrahedron Artin group; hyperbolic triangles (m,m,m)); G̃_2 as a B_A node (would add labels-3-and-6 graphs).
**Rule slip:** one accidental empty `python3 -` (stdin empty, no-op) inside a file-edit command at ~09:15; no output used.
Status: idle.
- FROM bh-verify-artin (bf75b2fe6): new OPEN node `d-tilde-artin-groups-satisfy-permutational-boone-higman` (not yet wired into artin-groups-satisfy-boone-higman — owner's call); new second proof of B̃_n (all n) `b-tilde-artin-groups-via-one-cone-point-fibration`; `euclidean-artin-toric-commensurability` + `weyl-toric-arrangements-b-d-e-f-are-not-fiber-type` (D̃_n, Ẽ, F̃_4 unreachable by toric bundles).
