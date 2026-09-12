---
rg: 2
id: rf-amenable-two-cell-telescope-proof
kind: route
title: Choose the regular quotient after the joint Følner window
target: rf-amenable-two-cell-retains-coefficient
requires:
  - amenable-multi-compressors-have-a-joint-hs-telescope
  - rf-hnn-telescope-retains-coefficient-residual
---

For a right Følner set `F`, collect the supports of `alpha_p(b)`, `p in F`,
and the corresponding iterates of any requested finite word window and
packet.  Injectivity makes all required pair differences nontrivial;
residual finiteness gives one finite quotient separating the whole finite
collection.

Use its regular representation on every block of the joint `P`-telescope.
The existing Følner block permutations give covariance error bounded by the
right boundary ratio and make every fixed semigroup relation hold away from
a finite union of such boundaries.  Meanwhile support separation gives on
every block

```text
||alpha_p(b)||_2^2=sum_g |c_g|^2.
```

Thus the joint telescope retains the exact canonical norm of `b` while all
covariance and amenable two-cell defects vanish.  For `b=z(1-a)`, the regular
bounded-type calculation supplies the fixed floor
`(1-epsilon)sqrt(tau_B(z))`.
For a coefficient-valued automorphic commutator, the base is normal and the
stable-letter quotient is amenable.  Hyperlinear-by-amenable permanence
therefore supplies canonical microstates of the whole extension, which
again retain the faithful regular norm of every nonzero base coefficient.
