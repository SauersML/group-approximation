---
rg: 2
id: pure-tensor-entangled-compact-counterexample
kind: claim
title: Pure C-star algebras can have a nonpure minimal tensor product through an entangled compact image
root: true
---

There exist pure C-star algebras `A` and `B` such that `A tensor_min B` is not
pure, witnessed by an irreducible representation of the tensor product whose
image contains a nonzero compact operator.

## Attempts

The implication from an entangled compact witness to this counterexample is
complete in `pure-tensor-entangled-compact-route`.  The sole missing input is
`pure-min-tensor-entangled-compact-witness`; its attempts section records why
spatial products and the maximal-tensor property-T diagonal construction do
not supply a minimal-tensor witness.  The witness is now also known to require
at least one nonsimple factor: `stw95-simple-pure-factors-exclude-compact-corridor`
rules out all simple-by-simple pure pairs by simplicity of their minimal
tensor product and reflection of type I from a tensor product to its factors.
