---
rg: 2
id: one-relator-group-cost-equals-first-l2-betti-plus-one
kind: claim
title: Infinite one-relator groups have cost equal to one plus the first l2-Betti number (Poulin--Wróbel)
artifacts:
  - research/artifacts/fpbs/poulin-wrobel-one-relator-cost-source-2026-09-11.md
distinct_from:
  fpbs-fixed-price-universal: that is Gaboriau's fixed price problem, about all free actions of a group having the same cost; this computes only the infimal group cost for one-relator groups and does not give fixed price for them.
  fpbs-graphing-cost-betti-cycle-dimension-identity: that is an identity for graphings relating cost, Betti numbers and cycle dimension; this is an exact computation of the group cost for one class of groups.
  fpbs-quotient-split-not-bernoulli-contained: that is the general obstruction that an action with a nontrivial factor fixed by a nonamenable normal subgroup is not weakly contained in the Bernoulli shift; this computes the cost of one-relator groups, and the source's Remark 3.6 is a finite-factor instance of the same mechanism (a nonergodic restriction to a nonamenable subgroup) for a different action.
---

**ESTABLISHED, BY CITATION (unrefereed preprint).** Let `Gamma = <S | w^m>` be
an infinite one-relator group, with `w` not a proper power and `m >= 1`. Then

```text
cost(Gamma) - 1 = beta_1^(2)(Gamma) = |S| - 1 - 1/m.
```

Source: Antoine Poulin and Konrad Wróbel, *Cost of one-relator groups*,
arXiv:2606.23506v1 (22 June 2026), Theorem 1.2. Here `cost(Gamma)` is the
group cost, the infimum of the costs of its free p.m.p. actions. This answers
a special case of Gaboriau's question on cost versus the first `l2`-Betti
number.

**Scope.** This does not establish fixed price for one-relator groups, and the
paper does not claim it. Its Remark 3.6 records why the method cannot: the
low-cost action built by the cutting method is not weakly contained in the
Bernoulli shift when the relevant subgroup is nonamenable, so it gives no upper
bound on the Bernoulli cost. For this class, fixed price is exactly the
statement that the Bernoulli shift has cost `|S| - 1/m`. See the source record
for the statements and the verbatim remark.
