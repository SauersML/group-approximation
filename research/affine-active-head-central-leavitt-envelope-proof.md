---
rg: 2
id: affine-active-head-central-leavitt-envelope-proof
kind: route
title: Split countably many regular active copies by S-linear renumbering maps
target: affine-active-head-central-leavitt-envelope
requires:
  - affine-s3-active-idempotent-toeplitz-envelope
  - affine-active-corner-has-faithful-binary-leavitt-envelope
---

Let `V` be a countable direct sum of the faithful left regular `S`-module.
Because `A` is central, `AV` is an `S`-submodule and is the direct sum of
countably many copies of `AS`. Partition those copies into the even and odd
submodules `W_0,W_1`. Copy renumbering gives `S`-linear isomorphisms
`s_i:AV->W_i`; let `t_i` be their inverses on `W_i` and zero on the other
summand. Extend all four operators by zero on `(1-A)V`.

They commute with the represented `S`, obey the support, inverse, and
range-sum relations in `(ACL1)`, while the original regular `S`-action stays
faithful. This proves injectivity. Finite presentation follows by imposing
commutation on a finite basis of `S`. The module-doubling and stably finite
conclusions are unchanged from
`affine-active-corner-has-faithful-binary-leavitt-envelope`.
