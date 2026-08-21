---
rg: 2
id: finite-index-double-theorem-misses-iwahori-twist
kind: claim
title: Finite-index double soficity does not cover the twisted Iwahori amalgam
distinct_from:
  iwahori-local-global-defect-question: that asks whether the twisted pair of vertex representations flexibly glues; this verifies that the 2024 finite-index DOUBLE theorem cannot decide it.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that gives the consequence if the Bass--Serre vertex action is sofic; this identifies why the closest graph-of-groups soficity theorem does not prove that hypothesis.
---

Let `C=PSL_2(Z)`, let `B_+` and `B_-` be the two index-three Iwahori
subgroups, and let

```text
sigma:B_+ -> B_-
```

be conjugation by `diag(sqrt(2),1/sqrt(2))`.  The amalgam

```text
C *_(B_+=B_-) C = PSL_2(Z[1/2])
```

is not an identity double covered by Gao--Kunnawalkam Elayavalli--Mj's
finite-index-double theorem: `sigma` does not extend to an automorphism of
`C`.

Indeed, with

```text
u=[[1,1],[0,1]],       ell=[[1,0],[1,1]],
```

one has `u in B_+`, `ell^2 in B_+`, and

```text
sigma(u)=u^2,          sigma(ell^2)=ell.
```

The abelianization of `PSL_2(Z)=C_2*C_3` is `C_6`; the image of `u` is a
generator.  An automorphism of `C` induces an automorphism of `C_6`, hence
sends that generator to another generator.  But `u^2` has order three in
the abelianization.  Therefore no automorphism of `C` restricts to `sigma`.

The same obstruction appears before quotienting the centre: in
`SL_2(Z)^ab=C_12`, the class of `u` is a generator while the class of `u^2`
is not.  Consequently the published theorem for identical edge embeddings
(including finite-index doubles) neither proves soficity of this amalgam's
Bass--Serre action nor refutes Iwahori stability.  A theorem allowing the
nonextendable edge twist is genuinely additional.

Primary source scope: Gao--Kunnawalkam Elayavalli--Mj,
[*On soficity for certain fundamental groups of graphs of groups*](https://arxiv.org/abs/2408.11724),
Theorem 1.2, Corollary 1.3, and the identical-embedding hypothesis in the
introduction.
