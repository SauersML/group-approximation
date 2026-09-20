---
rg: 2
id: leavitt-nonhyperlinear-from-compressor-normalization
kind: route
title: "Normalize the native Leavitt commutant and kill one explicit elementary matrix"
target: binary-leavitt-unit-group-is-not-hyperlinear
requires: [kazhdan-compression-pairs-normalize-all-tracial-models, leavitt-gl-equals-el-and-perfect-unit-group, elementary-groups-over-fg-rings-have-property-t]
artifacts:
  - research/artifacts/leavitt-direct-normalization-obstruction-2026-09-20.md
---

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf), Theorem 1.2/6.7, supplies the proposed universal internality input. Andreas Thom has priority for the conditional internality-to-normalization theorem; see his [*A conditional construction of a nonhyperlinear group and the centralizer problem*](https://andreasthom.github.io/pdf/nonhyperlinear.pdf), Theorem 1.2, and Liu Theorem 1.3/7.4 and its priority discussion. This route uses the normalization conclusion as an explicit prerequisite, not as an accepted unconditional import.

The binary Leavitt native subgroup L=diag(EL_3(R),1) is a Kazhdan compression subgroup of H=EL_4(R). The matrices u,k_+,k_- in the artifact are finitely many compressors and generate H together with L. With k=diag(I_3,1+et), one has k in C_H(L) and uku^-1=x_12(e). Thus normalization of D=pi(L)' forces pi(x_12(e)) into D. It commutes with pi(x_23(1)), so pi(x_13(e))=1. Since e is nonzero, this kills a fixed nontrivial element in every tracial-matrix-ultraproduct homomorphism and rules out hyperlinearity.

This proof needs neither heat rounding, scalar-commutant selection, character classification, simplicity nor finite presentation. The native Leavitt algebra is the earlier Cairn/OpenAI construction, not a construction claimed by Liu. Its application here is conditional on the fully credited normalization prerequisite.
