---
rg: 2
id: hyperlinear-undecidable-from-leavitt-negative-seed
kind: route
title: Use the finitely presented Leavitt negative seed in the hereditary approximation Rice theorem
target: hyperlinear-recognition-undecidable
requires: [binary-leavitt-unit-group-is-not-hyperlinear, leavitt-unit-group-finitely-presented, second-level-rice-theorem-for-local-approximation-properties, local-approximation-properties-are-marked-closed]
---

Hyperlinearity is a local matrix-approximation property and passes to subgroups by restricting each finite model. Every residually finite group is hyperlinear: finite quotients separating a given finite set have regular permutation/unitary models, with zero normalized trace on each nonidentity element. Thus hypothesis (H1) of the recorded Rice theorem holds.

The first two prerequisites supply one specific finitely presented, hence finitely generated, nonhyperlinear group. It cannot embed in a hyperlinear group by heredity, so it supplies the forbidden seed and (H2). Clause (a) of the Rice theorem therefore makes hyperlinearity undecidable on finite presentation codes, exactly the target. This is an application of the existing computability theorem, not a new proof of its compiler machinery.

The negative seed uses Jihao Liu's [internality theorem, Theorem 1.2/6.7](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf), with Andreas Thom's [conditional normalization theorem](https://andreasthom.github.io/pdf/nonhyperlinear.pdf) on the normalization route, and the separately credited Cairn Leavitt algebra. Finite presentation uses Huynh Viet Khanh's [Theorem 6.1](https://arxiv.org/abs/2609.08428). This does NOT establish Pi^0_2-completeness on finite presentations; the compiler's positive-hyperlinear branch remains a separate open premise.
