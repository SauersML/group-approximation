# bh-artin (BH swarm, Artin groups)
**Landed 4e7687670 (09-18 08:59), lane proofs, not reviewed:**
- artin-ordinary-foldings-are-retractions (+proof): edge-compatible foldings onto a standard parabolic are retractions; length map onto <v> for all labels.
- artin-pbh-reduces-along-folding-separators (+proof): A_Γ ∈ B_A iff both sides of a folding separation are; iff every block is. Example A(A_3) *_{A(A_2)} A(A_3) (single odd component, no cut vertex) ∈ B_A.
- forest-artin-groups-satisfy-permutational-boone-higman (+proof): forest-type Artin groups, any labels, ∈ B_A ⊂ fp-simple-embeddable.
- artin-groups-satisfy-boone-higman: status bullets + Attempt 5.
**Established status on main (read 09-18):** BH: RAAGs; spherical (all types, plain + B_A via char-0 linear); even FC and more (B_A); Ã_n, B̃_n, C̃_n, Euclidean triangles (B_A); forests (B_A, new). Open: D̃_n, Ẽ_6–8, F̃_4 (D̃_n: Roushon's poly-free claim relied on a Thm 2.14 corrected by Flechsig arXiv:2305.04273); odd 2-connected graphs without foldable separators (all-3 4-cycle); hyperbolic triangles; general FC and 2-dimensional; admissibly oriented (reduces to decidable-edge HNN permanence).
**Needs:** a tool for 2-connected odd graphs (one-sided retracts or HNN permanence over parabolics).
**Sparks:** arXiv:2603.15314 (CCFP) classifies parabolic-retractable Artin groups; its FC case is already Corollary E of the odd-component node. Its non-FC case needs B_A for odd complete graphs with divisible triangle labels (beyond (3,3,3)).
Status: idle (stall rule after one landing).
