---
rg: 2
id: atlas-a5-collision-seam-proof
kind: route
title: Transport the hidden radial involution and compute its normal closure in S4
target: atlas-a5-large-rectangle-cannot-share-marked-collision-seam
requires:
  - atlas-large-k22-has-faithful-a5-completion
  - atlas-full-large-rectangle-is-balanced-s720-two-cycle
artifacts:
  - experiments/atlas_a4_a5_atlas_nondevelopable.py
  - research/artifacts/atlas-a4-a5-atlas-nondevelopable.json
---

The verifier uses only exact permutation arithmetic.

For the frozen `A5` certificate it constructs `t=y^-1` and `s=b t^-1` and
checks that both marked radial subgroups have order six, that their
intersection has order two, and that its generator has the two word forms
in `(A5-SEAM-1)`.

It independently constructs the first-packet `S3 x S3` model.  Since `c`
lies in the second factor while `r,u,d` lie in the first, the commutator in
`(A5-SEAM-2)` evaluates to the identity.

Finally it uses the exact marked collision permutations

```text
t=(1 2 3),       s=(1 2),       c=(1 3)(2 4)
```

with GAP's product convention.  Exhaustive closure gives `|J|=24`,
`|<c,d>|=8`, and a nontrivial commutator.  Enumerating all its `J`-conjugates
and closing under multiplication gives a subgroup of order four containing
`c`.  Since the only normal order-four subgroup of `S4` is its Klein four,
this is exactly the claimed normal closure.  The contradiction uses no Todd
enumeration, low-index cutoff, or finite-target assumption.
