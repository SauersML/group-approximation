---
rg: 2
id: schur-rank-output-is-not-a-scalar-selector
kind: claim
title: A Schur rank-jump output cannot be cascaded as a scalar word of the same Boolean selectors
distinct_from:
  boolean-predicate-is-one-rank-jump: that successfully compiles a nonlinear predicate into representation dimension; this proves that dimension output cannot simply be read back as the scalar selector expected by another gate.
  finite-selector-gadget-induction-barrier: that rules out deleting selector characters by a finite overgroup; this is the cascading consequence for a rank gate whose local construction itself is valid.
---

Let `D=<z_1,...,z_k>` be a commuting Boolean selector subgroup and let
`f:{0,1}^k->{0,1}` be nonaffine. There is no group word `w` in the selectors
whose value on every character

```text
z_i |-> (-1)^x_i
```

is the scalar `(-1)^f(x)`. Hence the multiplicity jump

```text
T_x downarrow_A = S_x^(direct sum 2^f(x))
```

does not produce a canonical next-level Boolean group element carrying
`f(x)`.

Therefore a sequential Schur compiler cannot connect gates by naming each
rank output as the next scalar selector. It must transport the weighted
module multiplicity itself through a Morita/restriction incidence. Any
purported finite shift amalgam which identifies a derived nonlinear BCS
projection with a word in the original selector subgroup has silently
reintroduced the affine-selector impossibility.

