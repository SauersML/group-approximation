---
rg: 2
id: thompson-f-folner-function-exceeds-every-tower
kind: claim
title: C^-n-Følner sets of Thompson's group F have at least a tower of n exponentials of elements
distinct_from:
  thompson-f-is-amenable: that is the open amenability question; this is an unconditional lower bound on the size of Følner sets, and it is vacuous if F is not amenable.
---

**ESTABLISHED by citation.** J. T. Moore, *Fast growth in the Følner function
for Thompson's group F*, Groups Geom. Dyn. (accepted), arXiv:0905.1118v7
(8 Aug 2012), Theorem 1.1, verbatim:

> For every finite symmetric generating set Γ⊆F there is a constant C>1 such
> that if A⊆F is a C^−n-Følner set with respect to Γ, then A contains at least
> exp_n(0) elements.

Here `exp_0(n) = n` and `exp_(p+1)(n) = 2^(exp_p(n))`. The Følner function is
`Føl_(G,Γ)(n) = min{ |A| : A ⊆ G is 1/n-Følner with respect to Γ }`.

**Consequence.** If `F` is amenable, then `Føl_(F,Γ)(C^n) >= exp_n(0)`, so for
every fixed `k` the Følner function eventually dominates `exp_k`. Every family of
Følner sets whose size is bounded by a fixed tower of exponentials in
`1/epsilon` fails to be Følner for small `epsilon`.

Scope: statement and definitions read from the arXiv HTML render (ar5iv) of v7
on 2026-09-12. The proof was not re-read.

Citation route: `thompson-f-folner-tower-citation`.
