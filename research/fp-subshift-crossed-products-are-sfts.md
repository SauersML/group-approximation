---
rg: 2
id: fp-subshift-crossed-products-are-sfts
kind: claim
title: If the crossed-product algebra of a Z^2 subshift is finitely presented, the subshift is of finite type
distinct_from:
  sft-crossed-product-fp-iff-quantum-rigid: that characterizes finite presentation among SFTs by quantum rigidity; this shows that nothing outside SFTs can be finitely presented, so the characterization covers every subshift.
  minimal-subshift-crossed-product-is-not-finitely-presented: that excludes minimal Z-subshifts through LEF; this excludes non-SFT Z^2 subshifts through a commutative representation on locally admissible configurations.
artifacts:
  - research/artifacts/free-minimal-subshift-elementary-groups-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `k` be a field and `X ⊆ A^(Z^2)` a subshift. If
`LC(X, k) ⋊ Z^2` is finitely presented as a `k`-algebra, then `X` is an SFT.

**Proof.**
1. **Local presentations.** The local presentations `A_D` of
   `research/artifacts/sft-crossed-product-presentation-rigidity-2026-09-13.md` (Lemma 1) exist for
   any subshift. Finite presentation gives `A_D = R_X` for some `D`.
2. **A commutative model.** Let `Y_D` be the set of configurations all of whose `D`-ball patterns
   occur in `X`. Let `A_D` act sitewise diagonally on functions `Z^2 -> ℓ(Y_D)`. All relations of
   `A_D` hold.
3. **Descent.** The action therefore factors through `R_X`, which kills every non-occurring pattern
   of any radius. So `Y_D ⊆ X`, and `X = Y_D` is of finite type.

**Consequence.** Every subshift whose crossed product is finitely presented is an SFT. For SFTs,
finite presentation is exactly quantum rigidity. The first-order statement "finite presentation
forces finite type" is classical in spirit, and no novelty is claimed for it.

Route: `fp-subshift-crossed-products-are-sfts-proof`.
