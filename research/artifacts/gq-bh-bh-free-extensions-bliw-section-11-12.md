# BLIW Sections 10–12: reading record for the free-by-X lane (09-18)

Source: K.-U. Bux, C. Llosa Isenrich, X. Wu, *On the Boone–Higman Conjecture for groups
acting on locally finite trees*, arXiv:2408.05673v2 (24 Jan 2025). I read the text extracted on
MSI (`/scratch.global/sauer354/orbh-lit/2408.05673.txt`, 90,310 bytes, extracted 2026-09-12),
§§10.1, 10.5, 11, 12.1–12.5. Paraphrased statements, numbers as in the paper:

- **Lemma 10.1.** Let H_Λ ≤ G_Γ be a subgraph of groups with H_e = G_e for every edge e of Λ.
  If π_1(H_Λ) acts faithfully on its Bass–Serre tree, then π_1(G_Γ) acts faithfully on its own.
- **Theorem 10.5.** A graph of groups whose vertex groups are of type F_n and whose edge groups
  have finite index in the vertex groups, and whose fundamental group acts faithfully on the
  Bass–Serre tree, has fundamental group embedding in a simple group of type F_n.
- **Definition (§11).** For a group G, BS_G is the class of fundamental groups of finite graphs
  of groups all of whose vertex and edge groups are abstractly commensurable with G and all of
  whose edge inclusions have finite index.
- **Theorem 11.1.** Let G be of type F_n, n ≥ 2. If some nontrivial H ∈ BS_G acts faithfully on
  its Bass–Serre tree, then every K ∈ BS_G embeds in a simple group of type F_n (hence satisfies
  Boone–Higman). The proof glues the graphs of H and K along one new edge carrying a common
  finite-index subgroup, applies Lemma 10.1, then Theorem 10.5.
- **Theorem 12.1.** Torsion-free strongly scale-invariant G of type F_n (n ≥ 2): every group in
  BS_G embeds in a simple group of type F_n.
- **Theorem 12.2.** Every group in BS_Z embeds in a simple group of type F_∞.
- **Theorem 12.3.** For every k ≥ 1, every group in BS_{Z^k} embeds in a simple group of type F_∞.
- **Theorem 12.5.** For k ≥ 2, every group in BS_{F_k} embeds in a simple group of type F_∞; the
  faithful witness is a Burger–Mozes amalgam (their Theorem 12.6). The paper draws only the
  free-by-cyclic consequence from it.

Observation used by this lane: Theorem 11.1 needs only ONE faithful witness in BS_G, and BS_G
depends only on the commensurability class of G. Nothing else about G is used beyond type F_n.
