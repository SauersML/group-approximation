---
rg: 2
id: tailored-gap-is-lcs-or-has-a-nonaffine-edge
kind: claim
title: A tailored perfect gap is already an LCS gap unless one edge has a nonaffine full answer relation
distinct_from:
  zpc-readable-control-freezing-to-lcs: that seeks one invariant readable fiber and retains only the unreadable equations; this elementary dichotomy keeps the full answer variables and applies only when every complete edge acceptance relation is affine.
  affine-nested-odd-xor-selectors-force-affine-behavior: that obstructs aggregate decoding for a nonaffine behavior set; this proves that applying it to full answers loses no source-specific affine case, because the all-affine case already gives the desired LCS gap.
---

Let `G` be a finite tailored game with

```text
omega_ZIRS(G)=1,             omega*(G)<1.
```

For an edge `e=xy`, let

```text
A_e subseteq F_2^(S_x disjoint_union S_y)
```

be the complete set of accepted pairs of answers, including both readable and
unreadable coordinates.  Exactly one of the following holds.

1. Every `A_e` on an edge of positive verifier weight is affine.  Then `G`,
   with its tailoring forgotten, is already a finite binary LCS game.  The
   same perfect ZPC-IRS strategy is a perfect commuting strategy for this LCS,
   while its finite-dimensional quantum value is still `omega*(G)<1`.
   Hence the existing perfect-LCS-gap route already produces a
   non-hyperlinear solution group.
2. Some positive-weight edge has nonaffine `A_e`.  Any branch-complete
   shared-label compiler which aggregates the **full** active answers by odd
   XOR is then ruled out on that edge by
   `affine-nested-odd-xor-selectors-force-affine-behavior`.

Thus a source-specific finite-context rescue of odd-XOR aggregation cannot
come merely from the possibility that the full accepted relations of the
unknown TailoredMIP witness are accidentally affine: if they all are, the
main problem has already collapsed to LCS.  The only remaining affine escape
for an aggregate proposal is subtler: the projection of `A_e` onto unreadable
coordinates may be affine even though `A_e` itself is not.  Such a proposal
must still reconstruct a compatible readable answer, so it cannot claim
soundness from unreadable affine closure alone.
