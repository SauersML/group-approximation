---
rg: 2
id: atlas-literal-packet-common-mode-census-proof
kind: route
title: Expand every packet entry blockwise over rectangular F_2 maps and census the two-monomial equations
target: atlas-literal-packet-cannot-authenticate-any-common-mode
requires:
  - atlas-rank-five-complete-packet-exporter
  - atlas-mixed-minor-needs-nuisance-quotient-rank
---

**Structural expansion.**  For distinct indices `k != l` the block
`N=iota_k w p_l` satisfies `N^2=0`, and a product `N_t N_u` of two root blocks
is nonzero only when the target index of `t` equals the source index of `u`.
Therefore:

- `[x_ij(r),x_ij(s)]` and `[x_ij(r),x_kl(s)]` with `i != l`, `k != j` expand to
  `1`, so root and orth entries project to zero;
- `x_ij(a)^2=1+2N`, which vanishes over `F_2`;
- `[x_ij(r),x_jk(s)]=1+N M` with `N M` the composable path block, and
  `(1+NM)(1-R)=1+NM-R` because `NMR=0`, so an `st3` entry projects to `P=R`;
- a reverse entry `g=prod_t x_(k_t l_t)(b_t)` expands blockwise.  The four
  nontrivial seams have two factors on distinct blocks with vanishing
  products, and the eight one-factor rows give one block each.  So every
  block equation equates one generator block with one single-root occurrence.

Each nonzero equation has two terms with coefficient `+1` over `F_2`, i.e. it
is an equality of two monomials.  A vector constant on a connected component
of the incidence graph satisfies every such equation.  This proves `(LP3)`,
and with `atlas-mixed-minor-needs-nuisance-quotient-rank` it shows that no
literal family authenticates a common mode.

**Exact census.**  `experiments/atlas_packet_occurrence_rank_scan.py`
reconstructs the packet with the exporter and asserts the recorded word-list
SHA-256.  It recovers the root-level factor data of all 4,648 entries from the
three source generators, asserts the entry census
`root 200, orth 2980, st3 1432, inv 24, reverse 12`, and performs the blockwise
expansion by dynamic programming over composable letters.  It then computes,
with exact `F_2` elimination, the rank increment `rank[C D]-rank(D)` of every
right-hand-side star, taking desired columns to be the star's path monomials
and every other column to be nuisance.  It also checks common-mode survival,
and asserts the two hand-checked validation families (increments `0` and `2`).

On MSI (`python3 experiments/atlas_packet_occurrence_rank_scan.py
--characteristic 2`) it reports 1,448 projected equations (projected
equation-list SHA-256 `46558e0b…f5e648bb`) and 24 involutivity rows vanishing
in characteristic two. The equation histogram is `st3:terms=2` (1,432) and
`reverse:terms=2` (16). There are 320 two-letter stars, all of size three,
kind `st3` and increment two, with common mode surviving. There are 100
one-letter stars with increments `{1:20, 4:48, 5:32}`, the first above two at
`x_13(e)` (entries `3182,3186,3356,3360,3425`), all with surviving common
mode. The characteristic-zero rerun gives the same `st3` and reverse equations
and the same two-letter stars. The 24 involutivity rows survive there as
`2N=0`, which is an artifact of ignoring the packet's field, and one-letter
increments become `{1:20, 4:48, 5:8, 6:24}`.
Logs and JSON outputs are in the artifact.
