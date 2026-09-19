---
rg: 2
id: tracial-projective-hilbert-hotel-cancellation
kind: claim
title: Finite projective modules over a tracial matrix ultraproduct cannot be their own double
artifacts:
  - research/tracial-projective-hilbert-hotel-cancellation-proof.md
---

Let

```text
M=prod_omega (M_(d_n)(C),tr_(d_n))
```

be a tracial matrix ultraproduct.  If `P` is a finitely generated projective
right `M`-module, then

```text
P ~= P directSum P   implies   P=0.
```

More generally `P` cannot be isomorphic to `m>=2` copies of itself unless it
vanishes.  Consequently a unital action of any ring containing a binary
Leavitt family on a finitely generated projective `M`-module forces the
module to be zero.

This is the exact tracial Hilbert-hotel obstruction.  It does not by itself
decode group microstates into a coefficient module.
