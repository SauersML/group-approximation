---
rg: 2
id: gl-n-q-embeddings-detected-by-nontrivial-homomorphisms
kind: claim
title: A homomorphism from SL_m(Q) (m odd), Aff(Q), U_n(Q) or (Q,+) into any group is injective as soon as one named element survives
distinct_from:
  gl-n-q-targets-are-cofinal-in-n: that compares the inputs GL_n(Q), SL_n(Q), PGL_n(Q) under embedding; this shows that for these inputs an embedding is the same as a homomorphism that is nontrivial on one element, so constructions never need a separate injectivity proof.
  gl-n-q-embeds-in-fp-simple-group: that is the embedding target; this is an elementary reformulation of what a construction has to deliver.
---

**ESTABLISHED** by `gl-n-q-embeddings-detected-by-nontrivial-homomorphisms-proof`
(elementary, plus the classical simplicity of `PSL_m(Q)`; not independently
reviewed; no novelty claimed).

## Statement

Write `e_ij(q) = I + q E_ij`, `t_b` for the translation `x ↦ x + b` in
`Aff(Q) = Q ⋊ Q^x`, and `U_n(Q)` for the upper unitriangular group. Let `S` be
any group and `φ` a homomorphism from the named group into `S`.

1. **`(Q,+)`.** `φ` is injective iff `φ(1)` has infinite order.
2. **`U_n(Q)`, `n >= 2`.** `φ` is injective iff `φ(e_1n(1))` has infinite
   order. For `n = 3`, `e_13(1) = [e_12(1), e_23(1)]`.
3. **`Aff(Q)`.** `φ` is injective iff `φ(t_1) != 1`, iff `φ(Aff(Q))` is
   nonabelian.
4. **`SL_m(Q)`, `m >= 2`.** Every normal subgroup is central or everything.
   So `φ` is injective iff `φ(e_12(1)) != 1` and, for even `m`, `φ(-I) != 1`.
   **For odd `m`, `φ` is injective iff `φ(e_12(1)) != 1`.**
5. **`GL_n(Q)`, `n >= 2`.** Every normal subgroup consists of scalars or
   contains `SL_n(Q)`. So `φ` is injective iff `φ(e_12(1)) != 1` and `φ` is
   injective on the scalar subgroup `Q^x · I`.

## Consequence for the root

With `gl-n-q-targets-are-cofinal-in-n`: the root
`gl-n-q-embeds-in-fp-simple-group` holds **iff for infinitely many odd `m`
there are a finitely presented simple group `S` and a homomorphism
`SL_m(Q) -> S` with `e_12(1) ↦ nontrivial`.** The same holds with "finitely
presented simple" replaced by "finitely presented with a type (A) action"
(`gl-n-q-in-permutational-boone-higman-class`).

Stepping stones the same way:
- `Aff(Q)` embeds in `S` iff some homomorphism `Aff(Q) -> S` does not kill the
  translation `t_1`.
- `U_3(Q)` embeds iff some homomorphism sends `[e_12(1), e_23(1)]` to an
  element of infinite order.

**How to use it.** A construction may exhibit elements of `S` satisfying a
presentation of `SL_m(Q)`, for example the Steinberg relations together with
the `K_2(Q)` relations, and check one inequality. Elements satisfying only the
Steinberg relations give a homomorphism from `St_m(Q)`. Its nontrivial image is
a perfect central extension of `PSL_m(Q)`, and not `SL_m(Q)` unless the
`K_2(Q)` symbols die.
