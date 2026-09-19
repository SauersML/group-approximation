---
rg: 2
id: loop-braid-one-ring-push-link-contains-absorbed-block
kind: claim
title: "One-ring push of a cable vertex in the loop braid descending link: lk(b0) ∩ lk(A_vc b0) is not the types-avoiding-c part of lk(b0), but contains an absorbed-block family member X_{n−2}(F∪{c}) of free count N−3"
distinct_from:
  loop-braid-pair-twist-push-mutual-link: that pushes a vertex by a pair twist tau_br, which centralizes a triple-cable subgroup; this pushes a type-(v,w) vertex by the one-ring move A_vc, for which the triple-cable mechanism is unavailable, and the mutual link instead contains the image of an absorbed-block homomorphism A_cj -> A_cj A_vj A_wj
  loop-braid-forbidden-ring-coning-statement: that is an open connectivity statement about Y; this is a proved local fact about the pairwise intersections lk(b0) ∩ lk(A_vc b0) that its Björner nerve criterion uses, with no connectivity content
artifacts:
  - research/artifacts/zp-loop-braid-one-ring-push-absorbed-block-2026-09-17.md
  - experiments/loop-braid-one-ring-push-2026-09-17/stallings.py
  - experiments/loop-braid-one-ring-push-2026-09-17/one_ring_push.py
  - experiments/loop-braid-one-ring-push-2026-09-17/one_ring_push_output.txt
  - experiments/loop-braid-one-ring-push-2026-09-17/orbit_check.py
  - experiments/loop-braid-one-ring-push-2026-09-17/orbit_check_output.txt
---

Notation is from `zp-loop-braid-forbidden-ring-push-reduction-2026-09-17.md` (the w8 artifact).
- `P = PLB_n = PΣAut_n` acts on `X_n(F)` with strict fundamental domain Q.
- `A_ij : x_i ↦ x_j x_i x_j^{-1}`.
- v, w, c are distinct free rings, `b0 = [(v,w)]`, and `L := lk(b0) ∩ lk(A_vc b0)` in `X_n(F)`,
  with free count N.

**Claim.**
1. **(Literal (★) fails.)** For `n ≥ 5` and free rings `a, b ∉ {v, w, c}`, the vertex
   `A_ca[(a,b)]` lies in `lk(b0)` and has type avoiding c, but it is not in `lk(A_vc b0)`.
   - So L is not the types-avoiding-c subcomplex `X_{n−1}(F ∪ {f, c})` of `lk(b0)`, which is what
     w8 §7 (★) asked.
   - The certificate is the P-invariant `rank(p(C_u) ∩ q(C_z))`, with
     `C_(a,b) = ⟨x_a x_b, x_k (k ≠ a,b)⟩`. It takes the value n − 3 instead of the standard n − 2.
2. **(Absorbed block.)** The rule `A_cj ↦ A_cj A_vj A_wj`, with `A_ij ↦ A_ij` otherwise, defines
   an injective homomorphism `θ : PLB_{[n]∖{v,w}} → P_vw` that centralizes `A_vc` and `A_wc`.
   - θ induces a simplicial embedding `Φ : X_{n−2}(F ∪ {c}) ↪ L`, on the rings `[n]∖{v,w}`.
   - That complex has **free count N − 3**.
   - The image lies in `lk(A_vc^k b0)` for every k ∈ Z.

Whether equality `L = Φ(X_{n−2}(F ∪ {c}))` holds is not part of this claim. It is recorded as
conjecture (★′) in the artifact §4, with 5040/5040 agreement in random tests
(`absorbed_block.py`).
