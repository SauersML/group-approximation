---
rg: 2
id: steinberg-chord-fox-recurrence-has-zero-solutions
kind: claim
title: The two big-cell chord Fox recurrences have only the zero solution
---

For every odd prime `p`, the only function

```text
f:F_p^3 -> F_p
```

satisfying the two explicit equations `(SBC5)`, with boundary values read by
the signed tree-cut rule of `steinberg-cycles-have-big-cell-chord-coordinates`,
is `f=0`.

This is a strict coordinate form of the open Steinberg test.  It has exactly
three root parameters and no remaining panel-sum unknowns.  A proof may work
separately on the generic transformed chords and the exceptional affine
linear or bilinear loci where one of the transformed point/plane normalizing
coordinates vanishes; the latter terms are fixed cut-sums, not free boundary
data.  The seven generic rational transformations and all their exceptional
loci are recorded in `steinberg-fox-chord-actions-are-explicit`.

## Attempts

1. **Restrict to the six Weyl chambers.**  This does not define a subsystem:
   `x_12(2)` sends `s_1B` to a chamber with a nonzero lower-root parameter,
   outside the standard apartment.  Hence a Weyl-sign calculation drops
   terms of the actual recurrence.
2. **Use the constant/root-invariant chord vector.**  This is the
   `U^-`-fixed line.  Since `q` and `s` fix it, the first row acts as `-1`,
   so it supplies no common-kernel vector.  The opposite `B`-fixed line is
   killed by `Y`, but `X` sends its highest vector to a linear combination
   of three distinct PBW basis vectors, so it also fails.
3. **Propagate on the generic rational charts.**  Equation `(SCA4)` is a
   closed finite-difference system wherever all seven normalizing factors
   stay nonzero.  The deferred boundary is exact: at
   `1-2a=0`, `1-c=0`, `1-b=0`,
   `1+ac-b+c/2=0`, or `1+c=0`, one or more evaluations become signed sums
   over a whole tree cut.  A generic-orbit propagation argument is not a
   proof until it shows that these cut sums are forced by, rather than free
   from, the neighboring generic equations.
4. **Filter by ordinary polynomial degree.**  The fractional-linear maps in
   `(SCA2)` and the cut-sum boundary terms do not preserve that filtration.
   Clearing denominators also changes on the zero loci, so it cannot discard
   the tree-cut equations.
