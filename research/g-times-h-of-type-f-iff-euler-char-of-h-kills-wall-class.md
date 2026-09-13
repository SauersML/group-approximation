---
rg: 2
id: g-times-h-of-type-f-iff-euler-char-of-h-kills-wall-class
kind: claim
title: "For H of type F, G x H is of type F iff G is finitely presented of type FP and chi(H) kills the Wall class of G"
distinct_from:
  g-times-z-type-f-iff-g-f-infinity-with-finite-cd: that is the case H = Z, where chi(H) = 0 and the Wall class drops out; this covers every type-F factor H and shows the answer depends only on chi(H)
---

Let `H` be of type F with Euler characteristic `χ(H) ∈ Z`. For every group `G`,
`G × H` is of type F iff `G` is finitely presented, of type FP, and
`χ(H) · σ(G) = 0` in `K̃_0(ZG)`, where `σ(G)` is the Wall class of
`fp-type-fp-group-is-type-f-iff-wall-class-vanishes`.

Consequences:

- `χ(H) = ±1`, e.g. the free group of rank 2 (`χ = −1`): `G × H` is of type F iff
  `G` is of type F. So the analogue of Problem 1.21 with `Z` replaced by `F_2` has
  answer **yes**, unconditionally.
- `χ(H) = 0`, e.g. `Z^k` (`k ≥ 1`) or a torus-bundle group: `G × H` is of type F iff
  `G` is finitely presented of type FP. Problem 1.21 for any such `H` is the same
  question as for `Z`.
- `|χ(H)| ≥ 2`: "`G × H` of type F ⇒ `G` of type F" holds iff no finitely
  presented group of type FP has a nonzero `χ(H)`-torsion Wall class.

So the difficulty of Problem 1.21 comes from `χ(Z) = 0`. A factor with nonzero
Euler characteristic detects the Wall class up to torsion.

Credit: this is the algebraic form of S. M. Gersten's product formula for Wall's
obstruction (A product formula for Wall's obstruction, Amer. J. Math. 88
(1966)), specialized to aspherical factors. The formula was not re-read; the
proof route is self-contained.
