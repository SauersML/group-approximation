---
rg: 2
id: hilbert-hotel-group-algebra-fd-reflection-proof
kind: route
title: Apply exact compression invisibility to the regular module of the target algebra
target: hilbert-hotel-group-algebra-fd-reflection
requires:
  - hilbert-hotel-model-full-mf-radical
  - compression-defect-dies-in-finite-dimensions
---

The exact commutant theorem kills the Hilbert-hotel compression defect in
every finite-dimensional linear representation over every field.  Since
that defect normally generates `H`, every such representation of `H` is
trivial.

Given `phi:k[H]->A`, the units `phi(h)` act on the finite-dimensional vector
space `A` by left multiplication.  This is a finite-dimensional linear
representation of `H`, hence every `phi(h)` equals `1`.  Therefore `phi`
factors through augmentation.  Augmentation itself has one-dimensional
target, proving equality of the intersection of kernels.
