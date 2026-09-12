---
rg: 2
id: nondegenerate-clifford-skew-rings-have-no-finite-dim-reps
kind: claim
title: Clifford skew rings with nondegenerate form have no finite-dimensional representations, so marked-site separation cannot reach them
invalidates: [kun-thom-clifford-skew-rings-sf-via-marked-sites]
distinct_from:
  complete-graph-clifford-cover-center-dies-in-finite-quotients: that is group-level, saying finite quotients of the complete-graph cover kill eps; this is algebra-level, saying the anti-central factor has no finite-dimensional representation at all for every nondegenerate form, and draws the consequence for proof methods.
  rf-lamps-preserve-stable-finiteness-for-arbitrary-actions: that proves stable finiteness by separating maps into marked-site crossed products; this shows no such map leaves a nondegenerate Clifford skew ring.
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

Let `k` be a field with `char k != 2`, `X` an infinite `G`-set, and `S`, `q` as in
`clifford-cover-group-algebra-splits-into-wreath-and-skew-ring`. Suppose the form `b_S` on
`directSum_X F_2` is nondegenerate, as it is for the complete graph, the compressor graph and the
matching graph. Then:

1. `C_S tensor_k L` is simple for every field `L >= k`.
2. `A_S = C_S semidirect G` has no unital `k`-algebra map to any `M_n(L)`.
3. So `A_S` has no unital homomorphism into:
   - `M_n(k[E])`, for any group `E`, because the augmentation is a character;
   - any marked-site ring `R_r(H,j)` or `R_r(H,F,beta)` over a residually finite `H`;
   - any algebra with a finite-dimensional representation.

**Consequence.** The separating-family proofs of `rf-lamps-preserve-stable-finiteness-for-arbitrary-actions`
and `residual-lamp-quotients-handle-monomial-actions` cannot be transported to `A_S`, or to the matrix-lamp
wreath of `oriented-clifford-skew-rings-embed-in-matrix-lamp-wreath`. Any proof of stable finiteness must
separate with rings that have no finite-dimensional representation, such as rank ultraproducts. Those are
gated by `clifford-skew-ring-rank-models-give-linear-sofic-wreath`.

**ESTABLISHED 2026-09-12** by `nondegenerate-clifford-no-finite-dim-reps-proof`.
