---
rg: 2
id: promislow-group-is-not-left-orderable
kind: claim
title: Promislow's group is not left-orderable, by a four-term cycle forced by its two Klein relations
distinct_from:
  finite-index-subgroups-of-el-n-are-not-left-orderable: that excludes orders on finite-index subgroups of elementary linear groups via torsion and Witte Morris; this is a four-line computation from the two defining relations of Promislow's group.
  amenable-fg-simple-groups-are-not-left-orderable: that concerns simple amenable groups; Promislow's group is virtually abelian and far from simple.
  normal-generators-of-free-products-have-non-lo-syllables: that mentions Promislow's group only as an example of a torsion-free non-left-orderable group; this proves the property.
artifacts:
  - research/artifacts/bengi-wise-doubles-left-orderable-2026-09-16.md
---

Let

```text
P = < a, b | b^-1 a^2 b = a^-2,  a^-1 b^2 a = b^-2 >
```

be Promislow's group. `P` admits no left-invariant total order.

More precisely, the proof isolates a lemma valid in every left-ordered group:
if `c > 1` and `c^-1 s c = s^-1`, then `s^k < c` for every integer `k`. In `P`,
after replacing `a` and `b` by their inverses where needed, this yields
`c < c^2 = a^{2e} < d < d^2 = b^{2f} < c` with `c = a^e > 1` and `d = b^f > 1`.

Every group containing a copy of `P` is therefore not left-orderable.

*Remarks, not part of the claim.* The root node records that `P` is
torsion-free and virtually `Z^3`. With this claim, `P` is a torsion-free group
that is not left-orderable. The failure of unique products for `P` (Promislow,
Bull. London Math. Soc. 20 (1988), cited from a bibliography and not
re-fetched) is a stronger property and is not used here.
