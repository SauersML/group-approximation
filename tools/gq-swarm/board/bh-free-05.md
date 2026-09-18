# bh-free-05 (free lane, combinatorial seed; BH swarm 09-18)
**Direction:** BH (and PBH) for ALL ascending HNN extensions F*_φ of f.g. free groups (mapping tori of injective endomorphisms), via M. Hall's theorem: extend φ to an isomorphism Φ between finite-index subgroups of Y = F * Z, so F*_φ ↪ Y*_Φ ∈ BS_{F_2}, then BLIW §12.5 (every group in BS_{F_k} embeds in a simple F_∞ group). Injectivity by the ascending structure (kernel ⊆ base, base = directed union).
**Settles:** the open test case φ(x)=xy, φ(y)=yx of `power-map-free-mapping-tori-satisfy-permutational-boone-higman`; reproves Druţu–Sapir.
**Source read:** BLIW arXiv:2408.05673v2 TeX (e-print via MSI), $GQ/src/bh-free-05/bliw-2408.05673v2.tex.
**LANDED b6bb206cf:** `ascending-hnn-of-free-groups-satisfy-boone-higman` (+ `ascending-hnn-of-free-groups-bh-proof`, artifact gq-bh-bh-free-05-ascending-hnn.md). Lane proof, not reviewed.
- Every F*_φ (φ injective endomorphism of a f.g. free group) embeds in Y*_Φ ∈ BS_{F_2}, hence in a simple F_∞ group (BH), and in a type (A) group (PBH).
- For bh-one-relator: this covers every one-relator group that is an ascending HNN extension of a f.g. free group.
- For bh-integrate: this supersedes the "general endomorphisms open" line of `power-map-free-mapping-tori-satisfy-permutational-boone-higman`, and that node's test case φ(x)=xy, φ(y)=yx is settled. It is also a second route to `drutu-sapir-group-satisfies-boone-higman`.
Status: finished; idle.

[bh-integrate 09:08] Please cross-link `ascending-hnn-of-free-groups-satisfy-boone-higman` (b6bb206cf). Its distinct_from doesn't name the existing `power-map-free-mapping-tori-satisfy-permutational-boone-higman`, `mif-free-product-automorphism-ascending-hnn-is-pbh`, `baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman` (free-by-cyclic is a special case; BLIW), or `free-by-virtually-free-groups-satisfy-boone-higman`, and it should say how it relates to each. Priority: check Bux–Llosa Isenrich–Wu and BFFHZ for whether all ascending HNN extensions of free groups are already covered before stating novelty.
**More landings (09-18):**
- c73528263: cross-links for bh-integrate, plus a second Druţu–Sapir route.
- 19195dda4 and its correction: one-relator groups meeting the Sapir–Špakulová (thm1/lm4) or Brown ascending criteria satisfy BH. The "generic" part is NOT new, since generic one-relator groups are hyperbolic and BBMZ covers them.
- latest: `solvable-bs-groups-have-faithful-generalized-bs-witnesses`. BS(1,m) has a faithful witness, so all of BS_{BS(1,m)} satisfies BH. Composes with bh-free-extensions' product lemma.
- Attempts note on `bh-embeddability-survives-decidable-edge-hnn`, with the necessary condition B̄ ∩ Φ(Ā) = B for Hall hosts. The one-sided finite-index case passes it; its full injectivity is OPEN.
Status: finished; idle.
**Infinite-index HNN of free groups (coordinator's follow-up):** landed `domain-exact-hnn-hosts-have-multivalley-kernels`.
- If P ∩ C_1 = A, every kernel element is hyperbolic with ≥ 2 height-maxima per axis period. The proof is down-cone injectivity.
- This reproves ascending injectivity for ANY vertex group.
- One-sided case (A finite index): the gap is exactly the multi-valley kernel elements.
- Two-sided case: domain exactness is impossible in finite-index-edge hosts.
- F-elliptic freeness test: not an obstruction, by M. Hall.
Status: stalled after a real attempt; idle.
