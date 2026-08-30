---
rg: 2
id: finite-square-zero-packets-admit-cutdown-fusion
kind: claim
title: Finite square-zero packets admit compact cutdown fusion
---

Let `A` be a C-star algebra with no nonzero finite-dimensional
representations.  Let `x_1,...,x_n in A` satisfy `x_i^2=0`, let

```text
I=Ideal(x_1)+...+Ideal(x_n),
```

and let `h in I_+` and `delta>0`.  There is a square-zero `x in A` such that

```text
(h-delta)_+ in Ideal(x).
```

This is the exact finite-fusion frontier left by the established packet
theorem.  It is stated as an open claim; no fusion construction is presently
known in this generality.

## Attempts

- The direct sum of the `x_i` is square-zero in `M_n(A)`, but no general
  operation returns it to `A` while preserving the ideal of the prescribed
  cutdown.
- In fact one `2` by `2` stabilization always suffices, by
  `finite-packets-fuse-after-one-stabilization`.  The open step is exactly
  support-preserving destabilization of its orthogonal Pedersen pair, as
  characterized by `square-zero-cover-is-orthogonal-pedersen-pair`.
- The scalar sum `x_1+...+x_n` fails because the mixed products
  `x_i x_j` need not vanish.
- Replacing the packet by orthogonal source and range corners is exactly a
  two-divisibility problem, so assuming such corners would import the missing
  Global Glimm content rather than prove it.
