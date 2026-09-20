---
rg: 2
id: bc-counterexample-via-module-k-inexactness
kind: route
title: Refute trivial-coefficient Baum--Connes through a K-inexact module quotient over a non-exact group
target: baum-connes-counterexample-group-exists
requires:
  - some-nonexact-group-has-a-k-inexact-module-triple
  - k-inexact-module-triple-refutes-trivial-coefficient-bc
---

**Live.**
- `k-inexact-module-triple-refutes-trivial-coefficient-bc` (established) turns a K-theory
  exactness defect of `0 -> C_0(U) ⋊_r G -> C*_r(V ⋊ G) -> C*_r((V/W) ⋊ G) -> 0` into a
  group violating the conjecture with trivial coefficients: `V ⋊ G` or `(V/W) ⋊ G`.
- The open input is the defect itself,
  `some-nonexact-group-has-a-k-inexact-module-triple`.

The [liftable quotient formulation](some-module-quotient-has-a-nonzero-liftable-kernel-class.md)
is an equivalent route into that same input. With D=C/J the object is
`0≠z∈im(K_j(C)→K_j(D))∩ker(K_j(D)→K_j(B))`, not merely an algebra
kernel or an arbitrary K-class of D. The
[all-trace theorem](module-quotient-k0-defects-are-trace-invisible.md)
excludes bounded positive trace detection of its degree-zero part;
it does not invalidate this route.

**Why this is the natural home of expander counterexamples at trivial coefficients.**
- Coefficient failures come from non-K-exactness, and K^top is half exact
  (`amenable-kernel-bc-transfer-and-ktop-half-exactness`).
- With trivial coefficients no ideal is available, and ghosts vanish
  (`reduced-group-algebras-contain-no-nonzero-ghosts`).
- Group algebras of amenable-by-`G` groups are crossed products by `G`, and module quotients
  supply the short exact coefficient sequences to which the topological chase applies;
  their reduced crossed-product sequences need not be exact.
- The route is realized by a finitely generated group whenever `G` and `V` are finitely
  generated.
