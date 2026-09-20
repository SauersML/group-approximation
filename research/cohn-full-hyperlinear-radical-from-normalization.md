---
rg: 2
id: cohn-full-hyperlinear-radical-from-normalization
kind: route
title: "Normalize the universal Cohn compression pair and kill its normal generator"
target: cohn-rank-four-has-full-hyperlinear-radical
requires:
  - kazhdan-compression-pairs-normalize-all-tracial-models
  - elementary-groups-over-fg-rings-have-property-t
artifacts:
  - research/artifacts/full-defect-ring-hyperlinear-radical-audit-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorems 1.2/6.7 and 1.3/7.4, supplies the analytic
internality/normalization chain, with Andreas Thom credited for the
conditional normalization implication. This is a Cairn application of
that explicit prerequisite to its earlier universal-ring compression
algebra, not a new proof of Liu's theorem or a consequence claimed in
his paper.

## Why sufficient

For C=Z<s,a,t,b | ts=ba=1, ta=bs=0>, set e=1-st,
G=EL_4(C), and L=diag(EL_3(C),1). Both are finitely generated Kazhdan
groups by the property-(T) premise. The artifact gives explicit
elementary factorizations for u, k_+, k_-, c; in particular no GL=EL
import is needed. The elements k_+,k_-,c centralize L, uLu^-1<=L,
and G=<L,u,k_+,k_->, verified on every elementary coefficient r in C.

For any model rho, normalization of D=rho(L)' forces rho(ucu^-1)
into D. Since ucu^-1=x_12(e), this kills x_13(e). Its normal closure
is G: two Steinberg commutators give x_42(bea)=x_42(1), signed
permutations give every unit-coefficient root, and further commutators
give arbitrary coefficients. Thus rho is trivial. Composing any map
to a hyperlinear target with an ultraproduct embedding of its countable
image proves the hyperlinear-radical formulation.
