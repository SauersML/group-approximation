---
rg: 2
id: kl-violation-refutes-hyperlinearity-route
kind: route
title: Refute hyperlinearity of the Leavitt unit group by violating Kervaire--Laudenbach
target: non-hyperlinear-group
requires: [kervaire-laudenbach-holds-for-hyperlinear, kl-violating-equation-over-leavitt-unit-group]
---

If a one-variable equation of nonzero total exponent over `R^x = L_(F_2)(1,2)^x`
has no solution in any overgroup, then by
`kervaire-laudenbach-holds-for-hyperlinear` the group `R^x` is not
hyperlinear, which is an explicit nonhyperlinear group.

The OpenAI nonsofic chapter points this out itself: Kervaire--Laudenbach
"holds for every hyperlinear group ... Consequently, it would hold for `R^x`
if that group were hyperlinear, whereas its failure would exhibit a
nonhyperlinear group."  (Their citation for the KL statement is imprecise —
see the correction recorded on
`kervaire-laudenbach-holds-for-hyperlinear`.)

**Logical scope.**  Per the caution on `hyperlinear-nonsofic-group`, this
route bears on `non-hyperlinear-group` **only**.  Evidence that `R^x` is not
hyperlinear does not push Pestov's Question 3.4 toward "yes"; it removes
`R^x` as a Q3.4 candidate and leaves that question untouched.  Only the
flexible side is informative about Q3.4.

**Difficulty.**  Recorded honestly on
`kl-violating-equation-over-leavitt-unit-group`: no KL-violating equation is
known over any group whatsoever, so this route asks to refute the
Kervaire--Laudenbach conjecture.  It is recorded as a falsification
instrument and a standing structural constraint on nonhyperlinearity
arguments, not as a plausible line of attack.
