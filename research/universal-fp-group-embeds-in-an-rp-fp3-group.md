---
rg: 2
id: universal-fp-group-embeds-in-an-rp-fp3-group
kind: claim
title: "A universal finitely presented group embeds in a recursively presented group of type FP_3"
distinct_from:
  ffz-rp-fpn-embedding-gives-fp-fn-embedding: that is the implication from recursively presented FP_n hosts to F_n hosts at every level n; this is the hypothesis of that implication at n = 3, reduced to a single universal group
---

Let `U` be a universal finitely presented group: `U` is finitely presented
and contains a copy of every finitely presented group (Higman, *Subgroups of
finitely presented groups*, Proc. Roy. Soc. London Ser. A 262 (1961)). The
claim is that some recursively presented group `H` of type `FP_3` over `Z`
contains a copy of `U`.

**Why this is the level-3 crux.** It is equivalent to
`every-finitely-presented-group-embeds-in-an-f3-group`.

- An `F_3` host of `U` is finitely presented, hence recursively presented,
  and of type `FP_3`.
- Conversely, an `FP_3` host `H` of `U` contains every finitely generated
  recursively presented group, because each embeds in a finitely presented
  group (Higman) and so in `U`. That is the hypothesis of Theorem A of
  Fournier-Facio–Zaremsky (`ffz-rp-fpn-embedding-gives-fp-fn-embedding`) at
  `n = 3`.

Homological finiteness permits infinitely presented hosts. Leary's `FP_2`
embedding (Math. Ann. 372 (2018)) produces such hosts, and the source's
Remark 2.2 notes they are recursively presented when the input is. The
requirement of recursive presentability is what lets Theorem A pull the host
back inside `U`.

**Relation to Question 1.4 of the source** ("Does every finitely generated
group embed in a group of type FP_3?"). That question asks for `FP_3` hosts of
all finitely generated groups, recursively presented or not, and without
asking the host to be recursively presented. Neither statement is known to
imply the other.

## Attempts

- **Rope-trick hosts: dead.** Fournier-Facio–Zaremsky Theorem B
  (`higman-rope-trick-group-is-never-fp3`) shows `Hig_ι(U)` is never
  `FP_3(Q)`.
- **Recursively presented `FP_2` hosts from Leary's construction.** The first
  step of Leary's embedding embeds the double `F *_R F` in a group of type
  `FP_2` (Lemma 2.5 of Leary's *Subgroups of almost finitely presented
  groups*). The second step is the rope trick, which is dead above `FP_2`. No
  higher analogue of either step is known.
- **Ascending HNN extensions preserve `FP_n`, but they do not create it.**
  Theorem A's device converts a homological host into a homotopical one at the
  same level. It does not raise the level.
- **Open-claim wiring.** Lane z1-01-ffz-fp3 records the general
  graph-of-groups obstruction, the twisted rope trick over hosts with
  finite-dimensional rational `H_2` (dead), and the acyclic-host twisted
  container (open) on `every-finitely-presented-group-embeds-in-an-f3-group`.
  Any of them that produces a finitely presented `FP_3` container of `U` also
  proves this claim.
