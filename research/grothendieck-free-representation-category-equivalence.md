---
rg: 2
id: grothendieck-free-representation-category-equivalence
kind: claim
title: Grothendieck's theorem may upgrade the invisible quotient to a representation-category equivalence
artifacts:
  - research/artifacts/invisible-quotients-architecture-audit-2026-08-23.md
---

For every nonzero commutative ring `A`, restriction along `q: W_K -> P_K` is an
equivalence of categories

```text
q_A* : Rep_A(P_K)  ->  Rep_A(W_K),
```

`Rep_A` denoting finitely presented `A`-modules with a group action.

If true this is a strict strengthening of the `Hom`-level statements the
five-radicals theorem gives: a bijection on `Hom(-, GL_d(F))` compares objects
only, while an equivalence compares morphisms and extensions too, and it would
let the paper state its invisibility in Grothendieck's own currency rather than
in a hand-picked list of target classes.

## Attempts

The obvious attack is to quote Grothendieck's equivalence directly.  The
profinite half `W_K^ = P_K^` is already available -- it is automatic from
`Res_fin(W_K) = R_K` -- and Grothendieck's theorem is an *if and only if*, so
the equivalence would come for free with no new analysis.

What has to be checked before claiming it, and has not been: whether
Grothendieck's theorem applies to this map as stated.  Two hypotheses are at
risk.  Both groups must be finitely generated, which holds.  But the classical
statement is usually deployed for residually finite groups, and `W_K` is
emphatically not residually finite; whether the equivalence direction of the
theorem needs residual finiteness, or only finite generation, decides the
matter.  A module over `A[W_K]` need not have `R_K` acting trivially, so the
essential surjectivity of `q_A*` is not obvious by hand and really would be
carried by the cited theorem rather than by a direct argument.

Settling this is a literature question, not a research problem, and it is worth
an hour: if the theorem applies, the paper gains its sharpest formulation at
zero cost, and if it does not, the paper must not use Grothendieck's currency
and should say so explicitly.
