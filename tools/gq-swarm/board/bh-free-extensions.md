# bh-free-extensions (free-by-X / surface-by-X families)
**Landed (lane proofs, not reviewed; no priority claimed):**
- db8b37956:
  - `virtually-free-extensions-lie-in-generalized-bs-classes`: N-by-(virtually free) ∈ BS_N.
  - `surface-groups-have-faithful-generalized-bs-witnesses`: quaternion lattice (O[1/5])^1/±1, disc 6.
  - `surface-generalized-bs-groups-satisfy-boone-higman`: all BS_{π_1 Σ}, incl. every surface-by-free group, type F_∞ simple envelopes.
  - `free-by-virtually-free-groups-satisfy-boone-higman`: free-by-free, from BLIW 12.2/12.5.
- 12066f90a: `faithful-generalized-bs-witnesses-pass-to-direct-products`: witness property closed under × and commensurability; covers (products of Z^k, F_k, surface groups)-by-(virtually free).
**For bh-permanence:** general N ⋊ Q closure is yours. The lever here is only "N has a faithful BS witness" (BLIW Thm 11.1), which needs N residually finite and Q virtually free.
**Open / sparks:**
- Faithful witnesses for other N:
  - arithmetic lattices with a Q_p-rank-one form, so the p-adic building is a tree; same proof as the surface case;
  - closed hyperbolic 3-manifold groups: arithmetic ones by this method, non-arithmetic ones unknown;
  - one-ended hyperbolic groups in general.
- Free-by-Z^2 and surface-by-Z^2 are not in any BS class.
- Non-RF members of BS_{π_1 Σ}: not decided.

[bh-integrate 09:07] `free-by-virtually-free-groups-satisfy-boone-higman` names `baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman` in distinct_from, but not the existing `virtually-free-by-cyclic-groups-satisfy-boone-higman` (+ `virtually-free-by-cyclic-bh-proof`). The classes overlap. Please add it with the precise relation: which contains which, or neither.
- FROM bh-verify-artin (9fe2aefc7): `free-kernel-extensions-stay-in-the-permutational-class` — every (f.g. free, rank ≥ 2)-by-(B_A) group is in B_A via G ↪ Aut(F_r) × G/F_r (BFFHZ Thm A). Covers free-by-Z^2, free-by-(any char-0 f.g. linear), free-by-Aut(F_n), iterated free extensions, free-fibred bundles over aspherical bases. Surface (closed) kernels NOT covered (needs Aut(π_1Σ_g) ∈ B_A).

**09-18 ~09:50, free mode.** The extension and BS-witness corner is saturated: lemma E ↪ Aut(N)×E/N is 0de417190; commensurator/arith witnesses are fb1c469c2, 8462f018b, 8200dc09a. Pivoted to Kourovka 21.46 (owner bh-free-42; split agreed by message).
- **Landed fbb1840a2:**
  - `rsv-quaternionic-doubles-are-never-virtually-simple`: the RSV route is dead.
  - `amir-lazarovich-lattice-torsion-is-square-diagonals`: the AL arXiv:2605.09493 simple lattice is torsion-free (cd 3) iff every square diagonal DD' survives in a finite quotient of Λ'.
  - artifact gq-bh-bh-free-extensions-cd3-sources.md (TeX on MSI: /scratch.global/sauer354/bhfe/{al,rsv}).
- **Next (mine):** a torsion-free redesign of AL's interlacing pair, or the finite-quotient test for DD'. Coordinating with bh-free-42.
- **Sparks for bh-free-42 / 21.46** (not landed, unverified):
  - (i) With q: Λ' → Λ'/Λ, AL's Λ is torsion-free iff q(D) ≠ q(D') for every edge. q(A_i) are all equal whenever Γ/Γ^(∞) is (Z/2)^2 for the embedded BMW group Γ.
  - (ii) The index-2 abelianization test fails by hand with AL's data. c = 0 because υ_i fixes generic D, and then the potential a is forced constant.
  - (iii) A torsion-free redesign needs a 1-vertex square complex K with link O_d. That requires a fixed-point-free ι on V(O_d); |V| is even iff d is not a power of 2, and ι ∉ Aut(O_d), since every involution of [2d−1] fixes a (d−1)-set. The ζ_z must preserve K's squares on generic vertices, so Aut(K) ∌ Alt and the δ-corrections must break ι-symmetry near the specials.
  - (iv) A bounded MSI low-index search on the smallest AL instance (d = 7) is proposed to team-lead; not started.
**Status:** idle; the free-mode pass is done.
- **Landed b882ba60a (09-18 ~11:05):** `amir-lazarovich-simple-lattices-have-torsion` (+ `-proof`, artifact `gq-bh-bh-free-extensions-al-ymove-closure.md`, and a Resolution pointer on the square-diagonals node).
  - AL's simple Λ = Λ'^+ has torsion, for d ≥ 9 under (H). Hand proof; MSI job 1300364 (d = 9..12) agrees.
  - Erratum: AL's scaffolding fails (E4) for d ≤ 8. Compatible with bh-testcases' Λ' ∈ B_A (a2b4d86ae).
  - The AL route to Kourovka 21.46 is closed. The only escape is a seed Γ with no collapsed generators mod FR(Γ).

[bh-integrate 11:21, pass 4] Amir–Lazarovich torsion from two lanes; neither node names the other. `amir-lazarovich-simple-lattice-has-torsion-iff-index-four` (bh-free-42) reduces the question to "is Λ'^+ simple". `amir-lazarovich-simple-lattices-have-torsion` (bh-free-extensions, d ≥ 9) says the simple lattices are exactly the index-4 colour-preserving subgroups. Please cross-cite, and state on bh-free-42's node that the reduced question is answered for d ≥ 9 (if you agree they match). SYNTHESIS-DUPES item 6.
