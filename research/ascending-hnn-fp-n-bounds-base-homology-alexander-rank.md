---
rg: 2
id: ascending-hnn-fp-n-bounds-base-homology-alexander-rank
kind: claim
title: "If an ascending HNN extension G*_sigma is of type FP_n over a field k, then for j <= n the base homology H_j(G;k) has finite rank over k[sigma_*] modulo sigma_*-nilpotent classes, and 1 - sigma_*^m has finite-dimensional cokernel"
---

**ESTABLISHED** through `ascending-hnn-fp-n-bounds-base-homology-alexander-rank-proof`.

**Setting.** `G` is a group, `σ: G → G` an injective endomorphism, and
`H = G *_σ = < G, t | t g t^(−1) = σ(g), g ∈ G >` the ascending HNN extension.
Let `χ: H → Z` send `t ↦ 1` and `G ↦ 0`, and put `N = ker χ`. Let `k` be a field
and `s = σ_*` the induced endomorphism of `V_j = H_j(G; k)`. Put
`T_j = ∪_(m ≥ 1) ker s^m` (the `s`-nilpotent classes).

**Statement.** Suppose `H` is of type `FP_n` over `k`; for example, `H` is of
type `FP_n` over `Z`. Then for every `j ≤ n`:

1. `H_j(N; k) ≅ colim( V_j --s--> V_j --s--> ⋯ )` is a finitely generated
   module over `k[t, t^(−1)]`, with `t` acting through conjugation.
2. `V_j / T_j` has finite rank over `k[s]`:
   `dim_(k(s)) ( V_j/T_j ⊗_(k[s]) k(s) ) < ∞`. The rank equals the rank of the
   free part of `H_j(N; k)` over `k[t, t^(−1)]`.
3. For every `m ≥ 1`, `coker(1 − s^m)` on `V_j` is finite-dimensional, and so
   is `ker(1 − s^m)` on `V_(j−1)`.

**Use.** This is a necessary condition only. It turns "is `G *_σ` of type
`FP_3`?" into a question about `H_3(G; k)` together with the action of `σ_*`.
In particular it applies to Grigorchuk's finitely presented extension
(`grigorchuk-hnn-extension-is-fp-infinity`, Zaremsky Problem 1.12): if
`H_3(𝔊; F_2)` contains infinitely many classes that are independent over
`F_2[σ_*]` modulo `σ_*`-nilpotent classes, then that extension is not of type
`FP_3`.

**Calibration.** For `G = Z` and `σ = ×2`, `H = BS(1,2)` is of type `F`.
Here `V_1 = k` with `s = 2`, of rank 1 when `char k ≠ 2` and nilpotent when
`char k = 2`, and `V_j = 0` for `j ≥ 2`. Both cases satisfy the bounds. For
the first Grigorchuk group `𝔊` with Lysenok's substitution, `V_1 = F_2^3` and
`s` has rank 2, so `V_1/T_1` has rank 0 over `F_2[s]`. `V_2` is
infinite-dimensional (the Schur multiplier of `𝔊` is an infinite elementary
abelian 2-group), and `FP_2` of the extension forces it to have finite rank
modulo nilpotent classes. That is consistent with `σ` shifting the finitely
many families of Lysenok relators.
