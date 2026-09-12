---
rg: 2
id: stw72-chain-ideal-collapse-proof
kind: route
title: Exclude finite-dimensional representations and invoke the chain Global Glimm theorem
target: stw72-chain-ideal-wpi-is-purely-infinite
requires:
  - chain-ideal-lattice-solves-lxxiii
---

Weak pure infiniteness passes to quotients.  A nonzero finite-dimensional
representation of `A` would therefore give a nonzero finite-dimensional
weakly purely infinite quotient.  This is impossible: if `q` is a minimal
projection in a nonzero finite-dimensional algebra, then every fixed finite
multiple `n[q]` is finite in its Cuntz semigroup, whereas
`infinity[q]=sup_k k[q]` is not.  Hence `A` has no nonzero finite-dimensional
representations.

The established theorem `chain-ideal-lattice-solves-lxxiii` now applies and
gives the Global Glimm Property for `A`.  Kirchberg--Rordam's characterization
says that a C-star algebra is purely infinite exactly when it is weakly
purely infinite and has the Global Glimm Property.  Both conditions hold,
so `A` is purely infinite.
