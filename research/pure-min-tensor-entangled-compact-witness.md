---
rg: 2
id: pure-min-tensor-entangled-compact-witness
kind: claim
title: Pure factors admit a compact-bearing entangled representation of their minimal tensor product
---

There exist pure C-star algebras `A` and `B` and an irreducible representation

```text
pi:A tensor_min B -> B(H)
```

on an infinite-dimensional Hilbert space such that `pi(A tensor_min B)`
contains a nonzero compact operator.

## Attempts

- For an infinite ICC property-T group, the left-right representation and the
  diagonal Kazhdan projection produce a rank-one operator in the image of the
  **maximal** tensor product.  This does not descend to the minimal tensor
  product: the representation is the quasi-regular representation of
  `(Gamma times Gamma)/Diagonal(Gamma)`, and weak containment in the regular
  representation would force the diagonal subgroup, hence `Gamma`, to be
  amenable.  Infinite property-T examples therefore fail at exactly the
  tensor-norm gate.
- No spatial product can work, even with reducible factor representations,
  by `spatial-pure-factor-reps-have-no-joint-compacts`.
- The factors cannot both be simple by
  `stw95-simple-pure-factors-exclude-compact-corridor`.  Indeed, Takesaki's
  theorem makes their minimal tensor product simple; a compact-bearing
  irreducible image would make the product elementary, and type I then
  reflects to both factors, contradicting their purity.
- Exact selfless constructions are excluded by current tensor-selflessness
  permanence theorems.  The live counterexample direction is consequently a
  genuinely entangled min-continuous commuting representation with at least
  one nonsimple pure factor.
