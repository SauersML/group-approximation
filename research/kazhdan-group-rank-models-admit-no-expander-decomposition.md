---
rg: 2
id: kazhdan-group-rank-models-admit-no-expander-decomposition
kind: claim
title: Property (T) gives no rank-metric rounding, dimension expansion, or expander decomposition over F_2
distinct_from:
  rank-ultraproduct-compressors-conserve-fixed-right-ideals: that rounds pointwise-fixed subspaces for free, with no property (T); this shows almost-invariant subspaces that are not fixed do not round, even for Kazhdan groups.
  f2-linear-sofic-groups-kill-rigid-compression-defects: that is the open rank-row defect criterion; this removes one proof strategy for it, the expander decomposition of the models, as a consequence of property (T).
  kazhdan-rank-ultraproducts-can-have-diffuse-commutants: that is the ultraproduct statement about relative commutants and invariant right ideals; this is the finite-stage statement about rounding, dimension expansion and decompositions.
artifacts:
  - research/artifacts/kazhdan-rank-rounding-counterexample-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma = EL_3(F_2[t])` with `S = { e_ij(1), e_ij(t) }`, a Kazhdan
set. For `q = 2^k` and `F_2[alpha] = F_q`, let `rho_k : Gamma -> SL_3(F_q) <= GL_(3k)(F_2)`
be induced by `t -> alpha`. Each `rho_k` is irreducible over `F_2`. Put `W_m = S_m^3`,
where `S_m = span{1, alpha, ..., alpha^(m-1)}`, and `b(X) = sum_s (dim(X + rho_k(s)X) - dim X)`.

1. `b(W_m) <= 6` for every `m`. But `W_(floor(k/2))` is at distance at least `(3k-3)/2`
   from every invariant subspace.
2. **No rounding modulus.** No `delta(eps) -> 0` makes `eps n`-almost-invariant subspaces
   of honest `F_2`-representations of `Gamma` lie within `delta(eps) n` of invariant
   ones.
3. **Not dimension expanders.** Irreducible `F_2`-representations of `Gamma` are not
   uniform dimension expanders.
4. **Expander decompositions leak linearly.** Let `3 floor(k/2) kappa > 6`, so that `N`
   itself is not internally `kappa`-expanding. For every decomposition of `F_q^3` into
   independent subspaces `P_j` with leakage `Lambda = sum_j b(P_j)`, the internally
   `kappa`-expanding pieces have total dimension less than `20 Lambda / kappa`. So a
   decomposition whose expanding pieces carry `(1 - lambda)` of the dimension has
   `lambda > kappa/21`. Linear-size pieces with leakage `o(n)` stay non-expanding under
   rank perturbations `o(n)` of the models. The scope in this item was tightened on
   2026-09-12 by gk-verify-pos: for small `k` the decomposition `{N}` can be expanding
   with `Lambda = 0`, and the perturbation statement needs the leakage bound.

Over `C`, irreducible unitary representations of a Kazhdan pair `(S, kappa)` satisfy
`b(W) >= kappa^2 dim W / 4` for `dim W <= n/2`. The unitary argument needs a Hilbert
structure. So step (K) of the Hamming normalization proof, rounding into expanding
pieces, has no rank-metric form obtainable from property (T) alone. Mechanism:
multiplication by `alpha` is a companion-matrix shift, and its degree truncations are
almost invariant. The Theorem E subgroup `EL_r(F_2[x_1..x_d])` has the same models.

Proof: Sections 1-3 of the artifact.
