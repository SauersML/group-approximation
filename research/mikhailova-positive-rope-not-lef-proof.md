---
rg: 2
id: mikhailova-positive-rope-not-lef-proof
kind: route
title: Apply finite-presentation LEF rigidity to the nonseparable inner edge and inherit the obstruction through the outer HNN extension
target: mikhailova-positive-rope-is-not-lef
requires:
  - finitely-presented-centralizing-hnn-lef-criterion
  - mf-safe-finite-presentation-compiler
  - mikhailova-fiber-product-gives-regular-mf-benign-compiler
---

In the positive compiler branch, the inner base `K` is a finite direct
product of finite-rank free groups and the edge `L` is finitely generated.
Membership in its Mikhailova factor is undecidable, and membership in that
factor many-one reduces to membership in `L` by fixing the other direct-product
coordinates.  Thus `L` is not separable in `K`: a finitely generated separable
subgroup of a finitely presented group has decidable membership by dovetailing
enumeration of subgroup words with enumeration of separating finite quotients.

The group `Gamma=<K,v | [v,L]=1>` is therefore non-LEF by
[[finitely-presented-centralizing-hnn-lef-criterion]].  The outer rope is an
HNN extension with base `Gamma x Q`, so Britton normal form embeds `Gamma`
in the output.  Subgroups of LEF groups are LEF; hence the output is not LEF.
