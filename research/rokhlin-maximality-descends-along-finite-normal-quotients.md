---
rg: 2
id: rokhlin-maximality-descends-along-finite-normal-quotients
kind: claim
title: If W is Rokhlin-maximal and N is a finite normal subgroup, then W/N is Rokhlin-maximal
distinct_from:
  rokhlin-maximality-ascends-amenable-normal-extensions: that is the open ascent from W/N to W across an amenable kernel; this is the descent from W to W/N across a finite kernel, which is proved.
  bernoulli-rokhlin-maximality-passes-to-subgroups: that passes maximality to subgroups and up finite index; this passes it to quotients by finite normal subgroups, which are not subgroups in general.
  rokhlin-maximality-closed-under-local-embeddings: that moves maximality along injective partial multiplication tables; a quotient by a finite kernel need not locally embed into the group, for example when the extension does not split virtually.
artifacts:
  - research/artifacts/rokhlin-finite-kernel-quotient-formula-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by [[rokhlin-maximality-finite-quotient-descent-proof]].

Let `W` be countably infinite and `N ◁ W` finite. If uniform Bernoulli shifts over `W` have Rokhlin entropy equal to
their base entropy for every alphabet, then the same holds over `W/N`.

In Seward's labels: `INF(W)` implies `INF(W/N)`. Every free ergodic `W`-action `X` of finite entropy gives the free
ergodic `W/N`-action `X/N`, whose Rokhlin entropy is at least `|N| h^Rok_W(X)` and still finite
(`rokhlin-entropy-quotient-formula-for-finite-normal-subgroups`).

**Scope and model test.**
- The kernel must be finite for this argument. Descent along every quotient would be the open root
  `bernoulli-rokhlin-entropy-maximal-for-every-group`, since every finitely generated group is a quotient of a free
  group.
- Contrapositive use: a finite extension of a non-maximal group is non-maximal. If
  `leavitt-units-have-zero-rokhlin-entropy-supremum` were established, it would make every finite extension of
  `L_(F_2)(1,2)^x` non-maximal.
- The converse, ascent across a finite kernel, is the finite case of
  `rokhlin-maximality-ascends-amenable-normal-extensions` and stays open.

Section 3 of the artifact. The literature check was bounded (companion artifact, Section 4).
