---
rg: 2
id: jacobson-amenable-symbol-subgroups-are-amenable
kind: claim
title: A subgroup of the binary Jacobson elementary group is amenable exactly when its Laurent symbol image is, so the compression cell and the constants carry faithful models
distinct_from:
  binary-jacobson-finitary-whitehead-shift-is-marked-lef: that proves LEF for the finitary kernel with one balanced shift; this classifies amenability of all subgroups by their symbol image, and places the compression cell with the constants, and separately the tilted Toeplitz constants, in amenable subgroups retaining the head.
  sofic-kernel-amenable-quotient-permanence: that passes soficity from a sofic kernel through an amenable quotient; this uses the locally finite symbol kernel, where amenable-by-amenable is amenable.
artifacts:
  - research/artifacts/jacobson-rank-radical-support-bound-and-symbol-firewall-2026-09-12.md
---

**ESTABLISHED** by `jacobson-amenable-symbol-subgroups-amenable-proof`.

Let `J = F_2<S,T | TS = 1>`, `Q = 1 - ST`, and `pi : EL_n(J) -> EL_n(F_2[z, z^(-1)])` the symbol map
(`S -> z`, `T -> z^(-1)`).

1. **Theorem.** A subgroup `B <= EL_n(J)` is amenable iff `pi(B)` is amenable. The kernel meets `B` in
   a locally finite group of finitary matrices.
2. **The cell.** In `E_4 = EL_4(J)`, with the compressor `u` of `non_mf_groups_exist.tex`
   (`lem:ring-compression-cell`), `pi(u) = diag(z, z, z, z^(-3))`. So for every `Lambda <= EL_3(J)`
   with amenable symbol image, `<ker pi, u, Lambda>` is amenable.
3. **Instances.**
   * **Constants.** `Lambda = EL_3(F_2)` gives an amenable subgroup containing:
     * `u` and the cell element `c`;
     * the commutant cell `K_0` and its lamps (`jacobson-compression-cell-is-a-commuting-lamplighter`);
     * the finitary kernel and all constants;
     * the head `x_13(Q) = [u c u^(-1), x_23(1)]`.
   * **Tilted constants.** `Lambda = <x_12(T), x_23(T), x_21(S), x_32(S)>` has symbol image
     `diag(z, z^2, z^3) SL_3(F_2) diag(z, z^2, z^3)^(-1)`, a finite group.
4. **Faithful models.** These groups are sofic. So over every field they have injective rank models
   with `rk(sigma(g) - 1) >= 1/2` for `g != 1`, and they also have faithful Hamming and
   Hilbert–Schmidt models.

**Consequence.** Any proof of `binary-jacobson-el3-rank-radical-is-the-finitary-kernel`, in its rank-four
form, must evaluate the model on elements whose symbols generate a nonamenable group. Relations
inside any single subgroup with amenable symbol image cannot suffice. That covers the compression
cell with the constants, and the tilted constants with the cell. The smallest natural input is the
constants together with one Toeplitz root element, whose symbols generate `EL_3(F_2[z^(-1)])`. This
is where the operator-norm proof uses property (T), which has no rank form over `F_2`.
