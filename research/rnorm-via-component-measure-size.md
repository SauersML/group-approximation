---
rg: 2
id: rnorm-via-component-measure-size
kind: route
title: Dead - detect a strict compressor self-embedding of realized twists by a measure-type size on the space of Gamma-components
target: relative-normalization-modulo-kazhdan-kernel
requires:
  - component-measure-size-separates-compressor-images
---

**Dead.** Invalidated by `component-space-sizes-miss-leavitt-cover-defect`.

The plan was a Kun--Thom-style argument with counting replaced by measure:
- realized twists act on the measure space of `Gamma_s`-components;
- the compressor refinement factor and its fibre counts give one-sided monotone
  sizes;
- property (T) of `G` makes those sizes almost invariant, and a strict
  self-embedding `eps_t(Q_s) < Q_s` would change them.

On the hyperbolic Leavitt cover, which any proof of the target must handle, the
component space is pointwise fixed by `sigma(G)`. So the refinement factor is the
identity, compressed twists act on components exactly as the original twists do,
and host twists act as centralizer elements. No such size registers the defect.
