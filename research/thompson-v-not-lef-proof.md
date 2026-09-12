---
rg: 2
id: thompson-v-not-lef-proof
kind: route
title: Finitely presented plus LEF gives residually finite, which an infinite simple group is not
target: thompson-v-not-lef
requires: []
artifacts:
  - c1168433:official/counterexample.tex
---

## Why sufficient

Three facts, each standing on its own.

**`V` is finitely presented, infinite and simple.**  Cannon--Floyd--Parry,
Enseign. Math. 42 (1996); the simplicity of `V` is Higman's, and the finite
presentation is classical.  Finite generation, which is what the criterion
actually consumes, follows.

**Finitely presented and LEF implies residually finite.**  Vershik--Gordon,
Theorem 2.2.  Given a finite presentation with relator set `Rel` and a
nontrivial `g`, apply the LEF property to a finite `F` containing the
generators, `g`, and all subwords of the relators: the resulting local
embedding into a finite group is a homomorphism on that window, so it kills
every relator and factors through the presented group, while separating `g`
from `1`.

**An infinite simple group has no nontrivial finite quotient.**  Any
homomorphism to a finite group has kernel a normal subgroup, so trivial or
everything; trivial kernel is impossible for an infinite group.

Hence `V` is not residually finite, and therefore not LEF.

## The negative direction is the one that is used

Nothing here asserts that a non-LEF group must be nonsofic, or anything about
the soficity of `V` itself -- `V` is not known to be nonsofic, and this node
makes no claim either way.  What the criterion consumes is only the failure of
exact finite models.
