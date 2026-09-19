# Binary Leavitt unit group: LLP permanence audit (2026-08-21)

Primary source audited: Francesco Fournier-Facio and Rufus Willett,
*The Local Lifting Property, Property FD, and stability of approximate
representations*, arXiv:2603.18456v2 (April 2026).

For the subgroup input, Bleak--Salazar-Diaz, *Free products in R. Thompson's
group V*, arXiv:0911.0979, proves in particular that countable nonabelian free
groups embed in `V`.  The second commuting copy used below is the elementary
disjoint-cylinder construction in the binary-tree model of `V`; the faithful
embedding `V -> L_(F_2)(1,2)^x` is formalized in
`GroupApproximation/Leavitt/ThompsonVEmbedding.lean`.

The relevant statements are:

- Corollary 3.17: LP and LLP pass to subgroups;
- Corollary 3.19: LLP passes to directed unions of subgroups;
- Theorem 3.23 / Corollary 3.24 / Proposition 3.26: LLP passes through free
  products over finite-dimensional algebras, group amalgams over finite
  subgroups, and graphs of groups with finite edge groups;
- Theorem 3.39: if `1 -> K -> Gamma -> Lambda -> 1`, `C^*(K)` has LLP, and
  `Lambda` is amenable, then `C^*(Gamma)` has LLP;
- Question 1.6: whether `F_2 x F_2` has LLP (or LP) is open;
- Question 1.9: no infinite property-(T), or even infinite-relative-(T), LLP
  group is known.

Applied to `G=L_(F_2)(1,2)^x`, the positive constructions are circular:
finite generation collapses a directed union, `(T)` plus absence of finite
quotients collapses an amenable quotient, and property `FA` collapses a
reduced graph-of-groups decomposition.  Independently, the formalized
embedding `V <= G`, the standard disjoint-cylinder copies inside `V`, and
subgroup inheritance yield

```text
LLP(C^*(G)) => LLP(C^*(F_2 x F_2)).
```

This audit deliberately does not infer failure of LLP.  It records why the
Leavitt prefix/self-similarity presentation is not covered by any positive
permanence theorem in the cited source and calibrates a proof of LLP as at
least strong enough to settle its Question 1.6.
