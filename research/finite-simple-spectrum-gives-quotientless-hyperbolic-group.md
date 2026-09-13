---
rg: 2
id: finite-simple-spectrum-gives-quotientless-hyperbolic-group
kind: claim
title: A non-elementary hyperbolic group with only finitely many finite simple quotients forces a quotientless hyperbolic Kazhdan group
distinct_from:
  kazhdan-hyperbolic-group-without-finite-quotients: that is the open existence target; this is an established sufficient criterion whose hypothesis is a finiteness statement rather than an emptiness statement
  hyperbolic-group-without-finite-quotients: that asks for no nontrivial finite quotient at all; this shows that finitely many simple quotient types already suffice, so the two hypotheses are equivalent across the class of hyperbolic groups
---

**THEOREM (established; unreviewed).** Let `H` be a non-elementary word-hyperbolic
group with only finitely many isomorphism types of finite simple quotients, cyclic of
prime order included. Then there is an infinite word-hyperbolic group with property (T)
and no nontrivial finite quotient.

**Equivalence.** A quotientless infinite hyperbolic group has no simple quotients at
all. So across hyperbolic groups, "some non-elementary member has finitely many finite
simple quotient types" is equivalent to `hyperbolic-group-without-finite-quotients`, and
hence to `non-residually-finite-hyperbolic-group`.

**Scope.** Replacing non-elementary by infinite is false as a hypothesis for the
construction. The infinite dihedral group has only `C_2` as a finite simple quotient,
and the common-quotient theorem does not apply to it. The criterion bounds isomorphism
types only: arbitrarily large non-simple finite quotients are allowed.

Proof: `finite-simple-spectrum-gives-quotientless-hyperbolic-group-proof`. The argument
is §1–2 of `research/artifacts/hyperbolic-finite-simple-spectrum-construction-2026-09-12.md`
(landed by the 09-12 sweep; this node wires it into the graph). The geometric input is
`olshanskii-g-subgroup-quotient-theorem`.
