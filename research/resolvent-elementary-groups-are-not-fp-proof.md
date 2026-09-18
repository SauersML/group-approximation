---
rg: 2
id: resolvent-elementary-groups-are-not-fp-proof
kind: route
title: Corner symbols have infinitely generated stable image, which finite presentation of E_N forbids
target: resolvent-elementary-groups-are-not-fp
requires:
  - resolvent-ring-corner-symbols-survive-in-k2
  - infinitely-generated-symbols-block-fp-elementary-groups
---

1. `R_l` is a finitely generated ring, so the symbol lemma applies to it: part 1 of
   `infinitely-generated-symbols-block-fp-elementary-groups`, with `N >= 3`.
2. Suppose `E_N(R_l)` were finitely presented. By that lemma, the stable image `ι(K_2(N, R_l)) ⊆ K_2(R_l)` would be
   finitely generated.
3. The corner symbols `c(λ,μ)` lie in `K_2(N, R_l)`, and `ι(c(λ,μ)) = θ_*{λ,μ}`. These generate a subgroup that is
   not finitely generated (`resolvent-ring-corner-symbols-survive-in-k2`, part 3).
4. A subgroup of a finitely generated abelian group is finitely generated, which is a contradiction.
5. For `E_N(R_l)/C` with `C` finite: an extension of a finitely presented group by a finite group is finitely
   presented (P. Hall), as in part 2 of the symbol lemma. ∎
