---
rg: 2
id: fournier-facio-no-go-via-compression-subgroup
kind: route
title: A nonhyperlinear compression subgroup excludes every Fournier--Facio singular near witness
target: fournier-facio-has-no-purely-singular-free-near-representation
requires:
  - fournier-facio-hyperlinear-iff-singular-near
  - fournier-facio-compression-subgroup-not-hyperlinear
---

A purely singular essentially free near representation of `G` would make `G`
hyperlinear by the established equivalence, hence its subgroup `Gamma`
hyperlinear, contrary to the second prerequisite.

This route sits between `fournier-facio-nonhyperlinear-via-simple-factor`
(stronger input, `S`) and a genuine two-compressor argument (weaker input,
`G` only).  By `fournier-facio-one-compressor-subgroup-reduces-to-gamma`, it
is the route every one-compressor argument actually takes.
