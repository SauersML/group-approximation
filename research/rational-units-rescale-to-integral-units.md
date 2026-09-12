---
rg: 2
id: rational-units-rescale-to-integral-units
kind: claim
title: If every prime-field group ring of G is a domain, every unit of Q[G] is a rational multiple of a unit of Z[G]
distinct_from:
  rational-unit-conjecture-torsion-free: that asserts trivial units over Q for every torsion-free group; this is a coefficient-change lemma that proves no triviality and transfers units between Q and Z on one group.
  integral-unit-conjecture-torsion-free: that asserts trivial units over Z; this rescales units between Q and Z under a domain hypothesis.
  promislow-radius4-one-sided-and-integral-separation: that is a bounded-support unit census over F_2 with an integral lifting obstruction; this is a general Gauss lemma for group rings.
  kaplansky-all-fields-reduce-to-finite-fields-on-one-group: that transfers the domain property across fields on one tester group; this uses the domain property over prime fields as a hypothesis to transfer units from Q to Z.
---

**ESTABLISHED.** Let `G` be a group such that `F_p[G]` has no zero divisors
for every prime `p`. Then:

1. every unit of `Q[G]` is `c u` with `c in Q^x` and `u in Z[G]^x`;
2. `Q[G]` has a unit other than `lambda g` iff `Z[G]` has a unit other
   than `+-g`;
3. the rescaling does not move supports: `supp(c u) = supp(u)` and
   `supp((c u)^(-1)) = supp(u^(-1))`.

So on such a group every support-limited statement about units of `Z[G]`
(fixed support, fixed ball, one-sided or two-sided) is equivalent to the same
statement about units of `Q[G]`.

The hypothesis holds for every torsion-free elementary amenable group
(Kropholler--Linnell--Moody), in particular for the Promislow group `P`. On
`P`, then, the unit conjecture over the field `Q` and Higman's conjecture over
`Z` are one problem, ball by ball.

*Consequence for the framing in Tabei, arXiv:2608.02982v1, Section 5.1.* A
triviality theorem for `Z[P]` at word radius four would also be one for
`Q[P]`. It would separate `Q` and `Z` from `F_2` and `C`, but it could not
separate `Z` from the field `Q`.

DERIVATION
[[rational-units-rescale-to-integral-units-proof]]
