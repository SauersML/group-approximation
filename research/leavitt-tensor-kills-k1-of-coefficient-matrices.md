---
rg: 2
id: leavitt-tensor-kills-k1-of-coefficient-matrices
kind: claim
title: Every invertible matrix over B ⊗ 1 has trivial class in K_1(B ⊗ L_k(1,2)), for every ring B
distinct_from:
  leavitt-tensor-powers-have-trivial-k-theory: that asks for vanishing of all of K_1 and K_2 of the tensor powers; this is the elementary statement that the image of K_1(B) in K_1(B ⊗ L) is zero, which holds for every coefficient ring and is recorded there as the swindle that proves vanishing only on that image.
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that imports vanishing of all K-groups for regular supercoherent coefficients; this needs no regularity and covers only matrices with entries in B ⊗ 1.
artifacts:
  - research/artifacts/boone-higman-char-p-all-degrees-2026-09-12.md
---

**ESTABLISHED.** Let `k` be a field, `L = L_k(1,2)`, `B` a unital `k`-algebra
and `R = B ⊗_k L`. For every `N` and every `X ∈ GL_N(B ⊗ 1)`, the class of `X`
in `K_1(R)` is zero. Equivalently, `diag(X, I_j) ∈ E_(N+j)(R)` for some `j`.

This is the classical fact that `K_1(B) -> K_1(B ⊗ L)` is the zero map. It is
recorded as Attempt 3 on `leavitt-tensor-powers-have-trivial-k-theory`, the
corner swindle `φ(r) = e r e* + f r f*`, and no novelty is claimed. It is stated
here as a claim because the positive-characteristic linear class consumes it.

DERIVATION
leavitt-tensor-k1-coefficient-swindle-proof
