---
rg: 2
id: miller-fp-group-with-hereditarily-unsolvable-quotients-citation
kind: route
title: Import Miller's finitely presented group all of whose nontrivial quotients have unsolvable word problem
target: miller-fp-group-with-hereditarily-unsolvable-quotients
requires: []
artifacts:
  - experiments/ck-miller-poison-2026-09-17/kmss-miller-quote.txt
---

This is a citation import, not a reproof.

**Primary source.** C. F. Miller III, *Decision problems for groups -- survey
and reflections*, in *Algorithms and Classification in Combinatorial Group
Theory* (G. Baumslag and C. F. Miller III, eds.), MSRI Publ. 23, Springer,
1992, pp. 1--60. Miller's paper *The word problem in quotients of a group*
states a sharper form.

**Verbatim secondary statement.** Read on 2026-09-17 from the text layer of
I. Kapovich, A. Myasnikov, P. Schupp and V. Shpilrain, *Generic-case
complexity, decision problems in group theory and random walks*, J. Algebra
264 (2003) 665--694 (arXiv:math/0203239), printed p. 15:

> Using the existence of two disjoint recursively enumerable sets which are
> not recursively separable and the Adian-Rabin construction, C. F. Miller III
> [48] constructed an example of a finitely presented group G all of whose
> nontrivial quotients have unsolvable word problem!

Here [48] is the survey above. The excerpt and the reference entry are saved
in the artifact.

## Trust surface

- The primary texts were not read. Both returned HTTP 503 on 2026-09-17.
- The import rests on a verbatim quotation in a refereed survey-style
  paper by four specialists, which attributes the result to Miller. It is a
  well-known theorem.
- Only the bare existence statement is used downstream. The consumer
  `miller-amalgam-ck-envelopes-have-no-fng-maximal-kernel-proof` needs no
  information about torsion, orders of elements, or degrees of
  unsolvability.
