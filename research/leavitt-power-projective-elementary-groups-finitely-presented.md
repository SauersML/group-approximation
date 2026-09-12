---
rg: 2
id: leavitt-power-projective-elementary-groups-finitely-presented
kind: claim
title: For every prime p and every d the projective elementary groups of L_p^(⊗d) are finitely presented for infinitely many ranks
distinct_from:
  prime-field-leavitt-tensor-powers-have-trivial-k-theory: that is vanishing of K_1 and K_2 of the tensor powers, a sufficient condition; this asks only for finite presentation of E_m modulo its finite centre, where K_1 never enters.
  projective-elementary-fp-kernel-criterion: that is the general equivalence for an arbitrary finitely presented ring; this is the specific finite-presentation statement for Leavitt tensor powers that the positive-characteristic linear class needs.
artifacts:
  - research/artifacts/boone-higman-char-p-all-degrees-2026-09-12.md
---

**OPEN.** Let `p` be a prime, `L_p = L_(F_p)(1,2)` and `R_d = L_p^(⊗d)`. For
every `d >= 1` there are infinitely many `m` such that
`E_m(R_d) / Z(E_m(R_d))` is finitely presented.

With `char-p-linear-groups-embed-in-projective-leavitt-power-e-groups` this
settles `positive-char-linear-groups-satisfy-boone-higman`.

## Attempts

1. **`d <= 2` is known.** `K(L_p) = K(L_p ⊗ L_p) = 0`, so parts 2--3 of
   `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` give
   `E_m(R_d) = GL_m(R_d) ≅ R_d^x`, finitely presented for every `m`. Dividing
   by the finite centre preserves finite presentation.
2. **Vanishing low `K`-theory.** The route
   `leavitt-power-projective-e-fp-from-trivial-k-theory` gives every `d` from
   `prime-field-leavitt-tensor-powers-have-trivial-k-theory`.
   *Stops* at that claim for `d >= 3`.
3. **Unstable kernel.** `R_d` is a finitely presented ring, and `St_m(R_d)` is
   finitely presented for `m >= 4` (Krstić--McCool). The centre of `E_m(R_d)`
   is finite. So by `projective-elementary-fp-kernel-criterion`, the claim at
   `m` is equivalent to finite normal generation of
   `ker(St_m(R_d) -> E_m(R_d))`.
   - `K_1(R_d)` plays no role.
   - Finite generation of stable `K_2(R_d)` would suffice in a stable range
     where the kernel is central.
   *Not attempted beyond this reduction.*
