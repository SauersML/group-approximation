---
rg: 2
id: borel-two-q-is-units-times-aff-q
kind: claim
title: The Borel subgroup B_2(Q) is Q^x x Aff(Q), so B_2(Q) lies in B_A exactly when Aff(Q) does
distinct_from:
  gl-n-q-targets-are-cofinal-in-n: that compares GL_n, SL_n, PGL_n across n; this identifies the smallest Borel subgroup with a product of the stepping stone Aff(Q) and a countable abelian group.
  permutational-host-forms-agree-for-countable-inputs: that gives the host forms of B_A and puts every countable abelian group in B_A; this applies it to B_2(Q).
---

**ESTABLISHED** by `borel-two-q-is-units-times-aff-q-proof` (elementary; not
independently reviewed; no novelty claimed).

## Statement

Let `B_2(Q)` be the upper triangular matrices in `GL_2(Q)` and
`Aff(Q) = Q x| Q^x`, realised as `{[[a, b], [0, 1]]}`.

1. `B_2(Q) ≅ Q^x x Aff(Q)`, by `[[a, b], [0, d]] ↦ (d, [[a/d, b/d], [0, 1]])`.
2. Hence `B_2(Q)` lies in `B_A` iff `Aff(Q)` does, and `B_2(Q)` embeds in a
   finitely presented simple group whenever `Aff(Q)` lies in `B_A`.
3. For `m >= 2`, `B_(m+1)(Q) ≅ Q^m x| (B_m(Q) x Q^x)`, with `(A, d)` acting on
   `v in Q^m` by `v ↦ A v d^-1`. So `B_m(Q)` is an iterated affine group; it
   contains `Aff(Q)` and the divisible unitriangular group `U_m(Q)`, and it lies
   in `GL_m(Q)`. Any host of the root must host `B_m(Q)`, hence `Aff(Q)` and
   `U_m(Q)`.

Note (O4 on the root): hosts without distorted cyclic subgroups, such as `VA`,
cannot host `Aff(Q)` (it contains `BS(1,2)`), so they cannot host `B_2(Q)`
either.
