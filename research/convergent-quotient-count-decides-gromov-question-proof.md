---
rg: 2
id: convergent-quotient-count-decides-gromov-question-proof
kind: route
title: A finite count of simple quotients is a finite simple spectrum
target: convergent-quotient-count-decides-gromov-question
requires: [finite-simple-spectrum-gives-quotientless-hyperbolic-group, hyperbolic-rf-vtf-kazhdan-equivalence]
---

**(C1).** If `X(Λ) < ∞`, then `Λ` has finitely many normal subgroups with simple
quotient, and so finitely many isomorphism types of finite simple quotients.
`finite-simple-spectrum-gives-quotientless-hyperbolic-group` gives an infinite
hyperbolic Kazhdan group without nontrivial finite quotients. That is statement 3 of
`hyperbolic-rf-vtf-kazhdan-equivalence`. By that equivalence, statements 1 and 2 hold as
well: some hyperbolic group is not residually finite, and some hyperbolic group is not
virtually torsion-free.

**(C2).** The weights are positive on a finite set, so a weighted average of values in
`[0, ∞]` is finite only if every value is finite, and (C1) applies to any member.

If the average is `< 1`, some member has `X(Λ_x) < 1`, so `X(Λ_x) = 0`. That member has
no finite simple quotient. Every nontrivial finite group has a simple quotient, so it has
no nontrivial finite quotient.

**(C3).** This is the contrapositive of (C1): a quotientless infinite hyperbolic group is
not residually finite. So if every hyperbolic group is residually finite, `X(Λ) = ∞` for
each member, and each weighted average is infinite.
