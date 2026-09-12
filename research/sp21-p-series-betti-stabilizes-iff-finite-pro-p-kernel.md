---
rg: 2
id: sp21-p-series-betti-stabilizes-iff-finite-pro-p-kernel
kind: claim
title: The pro-p congruence kernel of an Sp(n,1) lattice subgroup is finite iff mod-p Betti numbers along its derived p-series eventually equal the p-adic dimension
distinct_from:
  sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel: that identifies finite rank of the pro-p completion with a finite kernel, through superrigidity; this reads finiteness of the same kernel off mod-p Betti numbers along one tower, by a Frattini argument with no superrigidity
  fpbs-lackenby-derived-p-series-largeness: that is Lackenby's theorem that linear mod-p homology growth along the derived p-series gives largeness; this characterizes the bounded regime, where mod-p Betti numbers are eventually the constant D
artifacts:
  - research/artifacts/sp21-torsion-growth-certificate-shape-2026-09-12.md
---

**ESTABLISHED.** Let `Γ`, `p` and `Γ(p)` be as in
`sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`. Let `Δ <= Γ(p)` have
finite index, and suppose its closure `U` in `∏_(v|p) G(O_v)` is uniform, of
dimension `D`. Every finite-index subgroup of `Γ(p)` contains such a `Δ` as a
normal subgroup of p-power index.

Let `N = ker(Δ̂_p ->> U)` be the pro-p congruence kernel. Let `D_i` be the derived
p-series of `Δ` (`D_0 = Δ`, `D_(i+1) = [D_i,D_i] D_i^p`), and put
`d_p = dim H_1(-;F_p)`. Then:

1. `d_p(D_i) >= D` for every `i`.
2. `N` is finite iff `d_p(D_i) = D` for all sufficiently large `i`.
3. If `N` is infinite, then `d_p(D_i) > D` for infinitely many `i`.

**With Theorem A.** By `sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel`:
- `Δ̂_p` has finite rank iff the mod-p Betti numbers of the derived p-series are
  eventually exactly `D`;
- the open claim `sp21-lattice-pro-p-completions-have-finite-rank` at `Δ` is
  equivalent to that eventual equality;
- neither side is a finite check.

**Consistency with (T).** In the finite-kernel regime, `d_p` along the derived
p-series is eventually constant. That is the extreme sublinear case allowed by
`fpbs-lackenby-derived-p-series-largeness`.

**Proof** (route `sp21-p-series-betti-stabilizes-iff-finite-pro-p-kernel-proof`,
artifact §3):
- The completion of `D_i` is `Φ^i(Δ̂_p)`, which maps onto `U^(p^i)`. This gives
  item 1.
- If `d_p` equals `D` at levels `i` and beyond, the Frattini quotients of
  `Φ^i(Δ̂_p)` and `U^(p^i)` are equal. So `N ∩ Φ^i` is contained in `N ∩ Φ^(i+1)`,
  and it stabilizes at `∩_j Φ^j = 1`.

**Inputs.**
- Property (T), for finite abelianizations. Theorem C itself uses no superrigidity
  and no cohomology theorem.
- Uniform-group facts from Dixon–du Sautoy–Mann–Segal, imported, not re-read.
- Ardakov–Brown arXiv:math/0511345 §2, read from the PDF.

No novelty claimed.
