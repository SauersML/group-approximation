---
rg: 2
id: weakly-sofic-not-sofic
kind: claim
title: Weakly sofic does not imply sofic
distinct_from:
  hyperlinear-nonsofic-group: that separates *hyperlinearity* from soficity and is open; this separates *weak soficity* from soficity and is now settled
  kun-thom-nonsofic-wreath: that is the nonsoficity input; this is the separation of approximation classes obtained by combining it with a weak-soficity permanence theorem
---

The class of weakly sofic groups strictly contains the class of sofic
groups.  A witness is the Kun--Thom wreath product
`W=(directSum_(G/Gamma) Z/2Z) semidirect G` for the explicit residually
finite Kazhdan pair of `kun-thom-nonsofic-wreath` Theorem E.

This answers the inclusion question that Glebsky recorded as open in 2023:
"It is an easy fact that all sofic groups are weakly sofic.  The other
inclusion is an open question."

## Why this belongs in this graph

It is the **first separation of any metric approximation class from
soficity**, and it is the exact shape of the statement Question 3.4 asks for
with `hyperlinear` in place of `weakly sofic`.  The permanence theorem that
supplies it (Glebsky, below) has **no hypothesis on the coset action** — in
contrast to every wreath-product permanence theorem available on the
hyperlinear side, each of which requires the action to be modelled by
permutations of a finite set:

- Hayes--Sale, arXiv:1608.02610 — standard wreath products, acting group
  must be sofic even when the conclusion is only hyperlinearity;
- Holt--Rees, Pacific J. Math. 287 (2017) 393--409, arXiv:1601.01836 —
  wreath closure proved for weakly sofic and separately for sofic,
  explicitly **not** for hyperlinear;
- Gao--Kunnawalkam Elayavalli--Patchell, arXiv:2401.04945 — generalized
  wreath products, requires the underlying set action to be sofic;
- Alekseev--Bradford, arXiv:2601.18742, Definition 4.23 — even for the
  hyperlinear class the action is modelled by `phi:Gamma->Sym(A)`.

So the live question for `hyperlinear-nonsofic-group` is sharp: does
Glebsky's residually-finite-by-weakly-sofic permanence have a
normalized-Hilbert--Schmidt analogue?  If "hyperlinear" could replace
"weakly sofic" in his Theorem 1.1, then `W` would be hyperlinear and
nonsofic, and Question 3.4 would be answered.
