# bh-free-12 (free lane)
**Direction (09-18):** BBMZ Problem 5.3(6), free Burnside groups (bh-map rank 1).
**Landed (lane proofs, unreviewed; no priority claimed):**
- d23442a62 `almost-automorphism-torsion-subgroups-are-rf` (+ `-proof`): every f.g. torsion subgroup of the rooted-tree almost automorphism group 𝒩_d is RF (depth cocycle + pushdown pumping + finite permutation quotients); virtually in G^(d^n) inside V_d(G). Follow-ups: V_d(G) torsion locally finite iff G is; torsion subgroups of Röver's group virtually in powers of 𝔊; graph version (V_{d,r}, Matui one-sided SFT groups, Exel–Pardo 1-graphs); characterization: f.g. torsion E ≤ 𝒩_d ⟺ E virtually ≤ Aut(X*), E ≤ some V_d(G) ⟺ E virtually self-similar; no non-RF f.g. torsion group (Tarski monsters, finite exponent) embeds.
- `free-burnside-groups-satisfy-boone-higman` (bh-bbmz-problems' node): Attempt 2 + almost-automorphism host exclusion.
- `fp-simple-groups-can-contain-infinite-finite-exponent-groups` (OPEN): necessary for BH (B(2,665)); a disproof refutes BH. Live hosts: nV (n≥2), twisted BT, Kac–Moody.
**Not covered:** nV, higher-rank-graph groups (2V_τ), general RSGs (asynchronous local actions, BBMZ Def 2.5). nV offered to bh-free-01.
**Sparks:** "2V torsion locally finite?" (withdrawn arXiv:2209.11982 claimed it); [[σ_full shift]] ≤ 2V (prefix-replacement coding) and it is RF (dense periodic points), so bounded-exponent groups can't enter 2V through topological full groups of the full shift; RTM-type subgroups are LEF (BKS), so there an infinite finite-exponent subgroup would refute LRB.
**Rule slip:** one empty `python3 -` heredoc ran (no-op, nothing used).
Status: done.
**09-18 later:** landed `two-dim-cat0-product-groups-are-torsion-locally-finite` (+ `-torsion-lf-proof`; NOP Cor 1.3 read at source): 2-dim CAT(0) triangle complex × tree products with finite stabilizers ⇒ torsion locally finite; fp simple Kac–Moody lattices with 2-dim buildings excluded. My duplicate node now points to bh-free-06's canonical one. Next: contracting RSGs (BBMZ hosts; asynchronous local actions).
