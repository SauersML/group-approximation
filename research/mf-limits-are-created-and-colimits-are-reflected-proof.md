---
rg: 2
id: mf-limits-are-created-and-colimits-are-reflected-proof
kind: route
title: Detect a nonidentity limit point in one coordinate and use the colimit adjunction
target: mf-limits-are-created-and-colimits-are-reflected
requires:
  - mf-radical-product-and-restricted-sum-formulas
  - mf-reflection-colimit-calculus
---

A group limit is a subgroup of the product of the objects in the diagram,
and its coordinate maps are jointly injective.  If `x!=1` in a countable
limit `L`, some coordinate image is nonidentity in an MF group.  Hence `L` is
residually MF and therefore MF.  Since the inclusion is full, the ordinary
limit cone has the same universal property against MF objects and is created
by the inclusion.

The colimit statement is exactly the MF reflection colimit theorem.  Applying
the two assertions to the standard limit and colimit presentations gives all
instances in `(LC1)`.
