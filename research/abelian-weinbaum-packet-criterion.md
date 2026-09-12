---
rg: 2
id: abelian-weinbaum-packet-criterion
kind: claim
title: A lattice test decides when one cyclic quotient retains the whole Weinbaum packet
distinct_from:
  one-relator-weinbaum-packet-amenably-visible: that asks for an arbitrary amenable locally indicable quotient for every relator; this gives a decidable sufficient-and-necessary condition for the quotient to be torsion-free abelian, and constructs a single cyclic target when it holds.
  rational-solvable-weinbaum-visibility-boundary: that uses the full rational derived series and a group-theoretic residual; this is a presentation-level integer-lattice test at the zeroth abelian layer.
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

Let `F=F(x_1,...,x_d)`, let `v` be cyclically reduced, and write
`e(u) in Z^d` for the exponent-sum vector of a word `u`.  Put

    L = Sat(Z e(v)) = (Q e(v)) intersect Z^d

(with `L=0` when `e(v)=0`).  For every `m>=1`, the following are equivalent:

1. there is a homomorphism from `F/<<v^m>>` to a torsion-free abelian group
   which is nontrivial on every proper nonempty contiguous subword `u` of `v`;
2. `e(u) notin L` for every such `u`;
3. there is one homomorphism from `F/<<v^m>>` to `Z` which is nontrivial on
   every such `u`.

Thus a finite computation with exponent-sum vectors closes the amenable
locally indicable packet gate for this presentation-visible family.  The test
is exact within all torsion-free abelian targets, not just sufficient.
