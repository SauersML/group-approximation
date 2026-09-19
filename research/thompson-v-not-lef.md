---
rg: 2
id: thompson-v-not-lef
kind: claim
title: Thompson's group V is finitely generated and not LEF
distinct_from:
  marked-quotients-not-lef: That is about the marked quotients of the non-MF manuscript's lamp construction, which are not simple and whose failure of exact finite models is proved from the marking; this is the classical fact for Thompson's `V`, from finite presentability and simplicity.
  permutation-norm-models-certify-exactly-lef: That identifies the class of groups certified by permutation operator-norm models, a statement about a certification method; this is a single group's failure of that property.
  leavitt-cylinder-swaps-generate-thompson-in-el: That places `V` inside an elementary prefix group over a Leavitt algebra, a membership statement with no approximation property in it; this is the non-LEF property of `V` itself, independent of any ring.
artifacts:
  - c1168433:official/counterexample.tex
---

ESTABLISHED, and classical.  Thompson's group `V` is finitely presented,
infinite and simple (Cannon--Floyd--Parry, *Introductory notes on Richard
Thompson's groups*, Enseign. Math. 42 (1996)), and every finitely presented
LEF group is residually finite (Vershik--Gordon, *Groups locally embeddable
into finite groups*, St. Petersburg Math. J. 9 (1998), Theorem 2.2).  An
infinite simple group has no nontrivial finite quotient, so `V` is not
residually finite, hence not LEF.

This is the non-LEF witness of the first nonsofic group
([[openai-leavitt-unit-nonsofic]]): a group that a sofic approximation would
be forced to make LEF, and cannot.

## A different witness from the one this development uses

This repository's own endpoint does **not** use simplicity.  Its witness is
the Higman-free two-relator obstruction
`Sofic/ThompsonFObstruction.not_isLEF_of_two_relations`: two noncommuting
elements satisfying the two standard Thompson-`F` relations
`[a b^(-1), a^(-1) b a] = 1` and `[a b^(-1), a^(-2) b a^2] = 1` force
`[a,b] = 1` in any finite group, because `c_n = a^(-n) b a^n` satisfies
`b^(-1) c_n b = c_(n+1)` and `n -> a^n` is periodic.  So the group they
generate is not LEF, and no identification with `F`, no finite presentation
and no simplicity is needed.

The two witnesses are worth keeping apart.  The route through simplicity needs
a finitely presented simple group and a citation for the presentation; the
two-relator route needs two group elements and a finite-group computation, and
is what a formalization can carry cheaply.  Either one closes the criterion.
