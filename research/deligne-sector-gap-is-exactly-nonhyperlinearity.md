---
rg: 2
id: deligne-sector-gap-is-exactly-nonhyperlinearity
kind: claim
title: The mod-three Maslov defect gap and one-word central collapse are each equivalent to non-hyperlinearity of the Deligne triple cover
artifacts:
  - research/artifacts/deligne-sector-tensor-camouflage-2026-08-21.md
distinct_from:
  deligne-central-mark-hs-collapse: that is the one-word analytic statement; this proves that, for this cover, the statement is equivalent to the terminal non-hyperlinearity conclusion by tensor camouflage in the converse direction.
  residual-finite-tensor-camouflages-iwahori-transfer-failures: that regularizes the character of an Iwahori transfer counterexample; this uses the same tensor principle to turn any mod-three projective almost representation into a faithful hyperlinear embedding of the central extension.
---

Let

```text
1 -> <z>=Z/3 -> E_3 -> Gamma=Sp_4(Z) -> 1
```

be Deligne's triple cover, and let `alpha` be the multiplier of a section.
The following are equivalent:

1. `E_3` is non-hyperlinear;
2. the `alpha`-projective presentation defect has a positive lower bound,
   uniform over all finite matrix dimensions;
3. the same holds in both nontrivial sectors `alpha` and `alpha^2`;
4. every normalized-HS almost representation of a fixed finite presentation
   of `E_3` sends `z` to the identity asymptotically.

Thus `maslov-mod3-projective-defect-gap` and
`deligne-central-mark-hs-collapse` are not weaker analytic stepping stones:
for this extension each is exactly the original non-hyperlinearity problem.
Deligne finite-dimensional invisibility shows only that zero defect is
unattainable in every fixed dimension.  It supplies no uniform separation
from zero as dimension grows.  Property (T) does not change this logical
equivalence.

The proof is `deligne-sector-gap-equivalence-proof`.
