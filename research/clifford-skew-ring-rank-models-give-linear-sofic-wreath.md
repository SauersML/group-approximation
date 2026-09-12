---
rg: 2
id: clifford-skew-ring-rank-models-give-linear-sofic-wreath
kind: claim
title: Rank embeddings of a nondegenerate Clifford skew ring make the Kun--Thom wreath and the Clifford cover linear sofic
distinct_from:
  kun-thom-wreath-linear-sofic: that is the open question whether the Kun--Thom wreath is complex linear sofic; this proves that a rank embedding of any nondegenerate Clifford skew ring over the same action would settle it, over any field.
  linear-sofic-group-algebra-is-stably-finite: that passes from linear soficity of a group to a rank embedding of its algebra; this passes from a rank embedding of a twisted factor to linear soficity of the untwisted quotient, through a tensor doubling.
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

Let `k` be a field with `char k != 2`, and `X` an infinite `G`-set on which `G` acts faithfully. Let `S`, `q`
be as in `clifford-cover-group-algebra-splits-into-wreath-and-skew-ring`, and `W = F_2 wr_X G`.

1. **Doubling.** `c_x tensor c_x^op` and `u_g tensor (u_(g^-1))^op` give an injective unital homomorphism
   `k[W] -> A_S tensor_k A_S^op`, for every `S`.
2. **Rank gate.** Suppose `b_S` is nondegenerate and `A_S` embeds unitally in a rank-metric ultraproduct
   of matrix algebras over `k`. Then `W` embeds in the unit group of such an ultraproduct, with every
   nontrivial element at positive rank distance from `1`.
   - If `W` concentrated near a scalar, `c_v u_g` would be rank-central, hence central, which is
     impossible.
   - For the Kun--Thom Clifford cover over `F_3`, `E_S` embeds the same way.
3. **Equivalence.** For the Kun--Thom Clifford cover with nondegenerate `b_S`, `E_S` is `F_3`-linear
   sofic iff `A_S` embeds unitally in a rank-metric ultraproduct over `F_3`.

**Consequences.**
- **Positive rank-model proofs.** Any proof that `A_S` is stably finite through rank models is at least as
  hard as linear soficity of the Kun--Thom wreath over the same field. Over `C` that is Arzhantseva--Paunescu
  Question 8.5, recorded as `kun-thom-wreath-linear-sofic`.
- **What a witness gives.** A one-sided inverse pair in `A_S` would prove `E_S` not `F_3`-linear sofic, and
  would say nothing about `W`.

**ESTABLISHED 2026-09-12** by `clifford-rank-models-linear-sofic-wreath-proof`.
