---
rg: 2
id: finite-hirsch-length-soluble-groups-hold-no-bs-chain
kind: claim
title: A soluble group of Hirsch length h has no element with h+1 infinite-order eigen-elements of distinct integer dilation rates, so no soluble group of finite Hirsch length (polycyclic, soluble minimax, or any iterated ascending HNN tower over Z) contains a Baumslag-Solitar chain configuration, and no ascending zoom-tower germ host can certify the chain group
requires:
  - chain-configurations-need-unboundedly-many-dilation-eigenvalues
  - zoom-tower-germ-groups-give-f-infinity-germ-extensions
distinct_from:
  chain-configurations-need-unboundedly-many-dilation-eigenvalues: that excludes hosts that are abelian over directed unions of fg metabelian groups with boundedly many associated primes, and leaves ascending towers of height four open; this excludes every soluble group of finite Hirsch length, which answers that question for towers of every height.
  higman-chain-group-pbh-iff-chain-configuration: that excludes linear and metabelian hosts by direct arguments; this excludes the finite-rank soluble hosts by one eigenvector count.
  zoom-tower-germ-groups-give-f-infinity-germ-extensions: that certifies germ extensions whose germ groups are ascending towers over the zoom; this shows those germ groups never hold a chain configuration, so that engine cannot reach the chain group.
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed).

For a soluble group `G` with derived series `G = G_0 ⊳ G_1 ⊳ … ⊳ G_d = 1`, put
`A_j = G_j / G_(j+1)` and `h(G) = Σ_j dim_Q (A_j ⊗ Q)`, the Hirsch length (torsion-free rank).

## Statement

1. **Eigenvalue bound.** Let `G` be soluble with `h(G) = h < ∞`, and let `b ∈ G`. Suppose
   `c_0, …, c_N ∈ G` have infinite order and `b^-1 c_n b = c_n^(λ_n)` for pairwise distinct integers
   `λ_n`. Then `N + 1 <= h`.
2. **No chain configuration.** No soluble group of finite Hirsch length contains a chain configuration
   `(a, b, c)` (`a^-1 b a = b^2`, `b^-1 c b = c^2`, `c` of infinite order). This covers:
   - polycyclic groups;
   - soluble minimax groups, and so constructible soluble groups;
   - every iterated ascending HNN tower `Z = H_0 < H_1 < … < H_r`, of any height `r`.
3. **Germ hosts.** No germ group that is an ascending zoom tower, as in
   `zoom-tower-germ-groups-give-f-infinity-germ-extensions`, contains a chain configuration. That engine
   therefore never certifies a host for `G_1`, `H4` or `BG`.

## Proof

- **Item 1.** For each `n`, let `j(n)` be the largest `j` such that some power `c_n^(m_n)`, `m_n >= 1`,
  lies in `G_j`. It exists because `j = 0` qualifies and `G_d = 1`.
  - The image `v_n` of `c_n^(m_n)` in `A_(j(n)) ⊗ Q` is nonzero. Otherwise some power of `c_n^(m_n)`
    would lie in `G_(j(n)+1)`.
  - Conjugation by `b^-1` preserves each `G_j` and acts `Q`-linearly on `A_j ⊗ Q`. It sends `v_n` to
    `λ_n v_n`, since `b^-1 c_n^(m_n) b = (c_n^(m_n))^(λ_n)`.
  - Eigenvectors with distinct eigenvalues are linearly independent. So at most `dim(A_j ⊗ Q)` indices
    have `j(n) = j`, and `N + 1 <= Σ_j dim(A_j ⊗ Q) = h`.
- **Item 2.** In a chain configuration, `c_n = a^n c a^-n` has infinite order and
  `b^-1 c_n b = c_n^(2^(2^n))`, by item 1 of `chain-configurations-need-unboundedly-many-dilation-eigenvalues`.
  These rates are pairwise distinct for all `n >= 0`, which contradicts item 1 for `N = h`.
- **Hirsch length of the listed classes.**
  - Polycyclic and soluble minimax groups have finite Hirsch length by definition of their series.
  - For towers, let `H` be an ascending HNN extension of a soluble `F`, and `L` the directed union of the
    copies `t^-k F t^k`. Every finite subset of `L^(j)/L^(j+1) ⊗ Q` lies in the image of
    `F_k^(j)/F_k^(j+1) ⊗ Q` for one copy `F_k`, so its dimension is at most that of `F`. Hence
    `h(L) <= h(F)`, and `h(H) = h(L) + 1` since `H/L ≅ Z`. By induction `h(H_r) <= r + 1`.
- **Item 3.** An ascending zoom tower is an iterated ascending HNN tower over `⟨z_p⟩ ≅ Z`. ∎

## What is left for hosts of the chain group

- **Infinite Hirsch length is forced for soluble hosts.** The candidate
  `M_1 = (⊕_(A/⟨b⟩) Z[1/2]) ⋊ BS(1,2)` of `higman-chain-group-pbh-iff-chain-configuration` has infinite
  Hirsch length, as it must.
- **Finitely presented soluble groups can have infinite Hirsch length.** Baumslag's finitely presented
  metabelian group contains `Z wr Z`. So finite presentation does not exclude a soluble host.
- **The open soluble route.** Does `M_1`, a finitely generated soluble group of derived length 3, embed
  in a finitely presented soluble group that lies in `B_A`? Both halves are open.
- **Germ hosts.** Germ hosts need germ groups that are not ascending towers. They must be soluble of
  infinite Hirsch length, or not soluble at all. The PL realization in
  `scale-periodic-bs-chain-germ-representations-are-not-faithful` is not a tower: its top letter pushes
  the zoom out of the affine stage. Whether its germ group is soluble was not examined.

## Lesson for general BH

**Rank is a spectrum budget.** In a soluble group of Hirsch length `h`, each element has at most `h`
independent dilation rates on infinite-order elements. Any input in which one element must dilate
infinitely many independent directions at distinct rates is excluded at once from every finite-rank
soluble host. This covers every tower host that BHM finiteness certifies cheaply. For such inputs a
host must have infinite rank. So its finiteness must come from a mechanism that does not see rank:
Theorem 2.1 with non-ascending SingFix groups, or finite presentations of infinite-rank soluble
groups, as in Baumslag's metabelian example.
