---
rg: 2
id: isomorphism-to-lamplighter-two-generator-recursive-is-pi2-hard
kind: claim
title: Recognizing the lamplighter Z wr Z among two-generator recursive presentations is Pi-zero-two hard, and the isomorphism problem for recursive presentations is Sigma-zero-three
distinct_from:
  shift-raag-family-classifies-amenability: that decides amenability of the family and identifies the amenable member as the lamplighter; this turns the identification into a statement about the isomorphism problem for recursive presentations.
  word-problem-solvability-rec2-is-sigma3-complete: that classifies decidability of the word problem on the family; this classifies isomorphism to one fixed group and bounds the general isomorphism problem.
---

ESTABLISHED.  For two-generator recursive presentations,

```text
{ e : G_e ~= Z wr Z }   is Pi^0_2-hard,                              (IS1)
```

and for pairs of **finitely generated** recursive presentations, each on a
fixed finite generating tuple, the isomorphism relation
`{(e, e') : G_e ~= G_{e'}}` is `Sigma^0_3`, because an isomorphism is
witnessed by two finite tuples of words.  So on finitely generated
recursive presentations isomorphism is between `Pi^0_2`-hard and
`Sigma^0_3`, whereas for finite presentations it is `Sigma^0_1`-complete
(a finite Tietze transformation).

**The countably generated case is not arithmetical at all.**  For
enumerated presentations an isomorphism is an infinite object and cannot be
guessed by a finite tuple; the corresponding index set is `Sigma^1_1`, and
by Downey--Montalban (*The isomorphism problem for torsion-free abelian
groups is analytic complete*, J. Algebra 320 (2008) 2291--2300, Theorem
1.2) already the isomorphism problem for computable torsion-free abelian
groups is `Sigma^1_1`-complete, hence so is the problem for enumerated
group presentations.  A cheap arithmetical lower bound in the same
direction: with `A_e = direct sum over {x : FiniteDomain(g(e,x))} of Z/2`,
which is enumerated uniformly in `e`, `A_e` is isomorphic to the fixed
group `direct sum over N of Z/2` iff that index set is infinite, a
`Pi^0_3`-complete condition, so enumerated isomorphism is already
`Pi^0_3`-hard and therefore not `Sigma^0_3`.

**Proof.**  (Finitely generated upper bound: two finite tuples of words,
each relator condition an r.e. derivation search under a universal
quantifier, so `exists (finite tuples) forall (relators) exists
(derivation)`.)  Hardness: the shift right-angled Artin family
[[shift-raag-family-classifies-amenability]] has `G_J ~= Z wr Z` iff
`J = Z_{>0}` (if `J = Z_{>0}` the kernel is free abelian on the shift
orbit and the group is the lamplighter; if `J != Z_{>0}` the group is not
amenable while `Z wr Z` is), so `e |-> G_{J_e}`, `J_e = {j+1 : j in W_e}`,
reduces `TOT` to (IS1).  Upper bound: `G_e ~= G_{e'}` iff there are words
`u_i` in the generators of `e'` and `v_j` in those of `e` such that every
relator of `e` maps to a trivial word of `e'`, every relator of `e'` maps
to a trivial word of `e`, and the two composites fix each generator; each
clause is "for every enumerated relator there is a derivation", `Pi^0_2`,
and the existential over the finitely many words makes it `Sigma^0_3`.
The `Sigma^0_3` upper bound for the finitely generated syntax is a
corollary: whether it is sharp there is open here.
