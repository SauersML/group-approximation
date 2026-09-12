---
rg: 2
id: prefix-support-contraction-proves-no-finite-boundary-submodules
kind: route
title: Force an impossible finite tail set and pass the obstruction through exterior contraction
target: bit-level-chart-pair-has-no-finite-boundary-submodules
requires: []
artifacts:
  - research/artifacts/kaplansky-bit-level-transporter-without-finite-boundary-modules-2026-09-08.md
---

Any finite-dimensional K-invariant subspace of the free boundary
module has support union {1,2,3,4} x T for a finite set of tails:
evaluation at each tail is equivariant into the irreducible natural
F_2 representation of K. For an H-invariant subspace, g sends this
support union to another of the same form. The fixed roots 3,4
force the two tail sets to agree.

The prefix 1->10 then makes the finite tail set closed under prefixing
zero, forcing every tail to be 000.... The rule 20->11 forces 1000...
into that same set. Hence the original subspace must be zero.

For a finite-dimensional invariant subspace in positive exterior
degree, iterated contractions span a nonzero finite-dimensional
invariant subspace of the original boundary module, giving the same
contradiction. No division is used. Finite scalar extension cannot
introduce such a submodule, by projection onto the original module's
copies after restricting scalars.
