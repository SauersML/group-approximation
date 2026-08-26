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

and for pairs of recursive presentations the isomorphism relation
`{(e, e') : G_e ~= G_{e'}}` is `Sigma^0_3`.  In particular the isomorphism
problem for recursively presented groups is not `Sigma^0_1` as it is for
finite presentations, where isomorphism is witnessed by a finite Tietze
transformation, and not `Pi^0_2`-easy either: it is `Pi^0_2`-hard already
against one fixed target.

**Proof.**  Hardness: the shift right-angled Artin family
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
The `Sigma^0_3` upper bound is a corollary: whether it is sharp is open
here.
