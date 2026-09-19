---
rg: 2
id: loop-braid-pair-twist-push-complexity-fails
kind: claim
title: "No complexity on X_n(F∪{v,w}) is lowered by pair-twist pushes with zero set in lk([(v,w)]): the antisymmetric clasp φ_ab = χ_{z,u} − χ_{u,z} is push-invariant"
distinct_from:
  loop-braid-pair-twist-push-mutual-link: that computes the mutual link of one pair-twist push and excludes types by the clasp χ_{u,z}; this shows the antisymmetrized clasp χ_{z,u} − χ_{u,z} is invariant under all such pushes, so no sequence of them can terminate in lk(b_0)
  loop-braid-descending-links-are-increasingly-connected: that is the connectivity target, which stays open; this refutes one method of proof and says nothing about the truth of the target
artifacts:
  - research/artifacts/zp-loop-braid-cx-antisymmetric-clasp-obstruction-2026-09-18.md
  - experiments/loop-braid-cx-obstruction-2026-09-17/antisym_clasp.py
  - experiments/loop-braid-cx-obstruction-2026-09-17/antisym_clasp_output.txt
---

Notation is that of `loop-braid-push-complexity-statement`:
- `P = PLB_n`, and `X^0 = X_n(F ∪ {v,w})` with base vertex `b_0 = [(v,w)]`;
- `e_ij(p)` is the exponent sum of `x_j` in the conjugator of `p(x_i)`;
- the pushes are `p[(a,b)] ↦ p g [(a,b)]`, with `g ∈ {τ_br, τ_ra}` a pair twist.

For distinct rings a, b outside `{v, w}`, put
`φ_ab := e_av − e_bv − e_aw + e_bw − e_va + e_vb + e_wa − e_wb`.

**Claim.** Suppose the free count is `N ≥ 4` and v, w are free.

1. `φ_ab` is a homomorphism `P → Z`. It vanishes on `P_{(a,b)}`, `P_{(v,w)}`, `P_{(w,v)}` and on
   every pair twist `τ_cd`, and `φ_ab(A_av) = 1`. So `Φ(p[(a,b)]) := φ_ab(p)` is well defined on
   type-`(a,b)` vertices. It is preserved by every pair-twist push, and it is constant on the
   type-`(a,b)` vertices of `lk(β)` for each vertex β of type `(v,w)` or `(w,v)`. That constant is 0
   for `β = b_0`.
2. No `c : V(X^0) → Z_{≥0}` satisfies (CX0) and (CX1). In particular CX(N) is false for every
   `N ≥ 11`.
3. For each `m` with `2m + 4 ≤ N`, the suspension `{[(a,b)], A_av[(a,b)]} * J`, with J a
   cross-polytope `(m−1)`-sphere in Q on 2m further rings, is an injectively embedded m-sphere in
   `X^0`. No finite sequence of Φ-preserving vertex moves carries it into `lk(β)` for any vertex β
   of type `(v,w)` or `(w,v)`. Pair-twist pushes are Φ-preserving.
