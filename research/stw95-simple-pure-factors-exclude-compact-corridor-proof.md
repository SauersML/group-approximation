---
rg: 2
id: stw95-simple-pure-factors-exclude-compact-corridor-proof
kind: route
title: Combine Takesaki simplicity with type-I reflection
target: stw95-simple-pure-factors-exclude-compact-corridor
requires:
  - takesaki-simple-minimal-tensor-simplicity
  - type-i-minimal-tensor-reflects-to-factors
---

Takesaki's theorem makes `D=A tensor_min B` simple.  Suppose an irreducible
representation `pi:D->B(H)` contains a nonzero compact operator.  The
irreducible-compact lemma gives `K(H) subset pi(D)`.  Simplicity makes `pi`
faithful and makes `K(H)` a nonzero ideal equal to all of `pi(D)`.  Hence

```text
D isomorphic K(H),
```

so `D` is type I.

By `type-i-minimal-tensor-reflects-to-factors`, both `A` and `B` are type I.
A nonzero simple type-I C-star algebra is elementary.  But a pure algebra is
nowhere scattered and therefore cannot itself be elementary.  This
contradiction proves the assertion.  It obstructs the proposed counterexample
engine; it does not prove that `A tensor_min B` is pure.
