---
rg: 2
id: sofic-recognition-two-generator-recursive-is-pi2-complete-proof
kind: route
title: Instantiate the second-level Rice theorem at soficity with the finitely presented nonsofic seed
target: sofic-recognition-two-generator-recursive-is-pi2-complete
requires:
  - second-level-rice-theorem-for-local-approximation-properties
  - sofic-recognition-has-a-pi2-upper-bound
  - finitely-presented-nonsofic-group-exists
---

Soficity is a local approximation property (the model predicate is
`Covers.TableCover.TableModel`).  (H1): residually finite groups are sofic
(`Sofic.SoficPositiveControl`), and in particular `B2(1)` is.  (H2): a
finitely presented nonsofic group exists
([[finitely-presented-nonsofic-group-exists]],
`Endpoint/MainResults.exists_finitelyPresented_nonsofic_group`).  Clauses
(b) and (c) of [[second-level-rice-theorem-for-local-approximation-properties]]
give `Pi^0_2`-hardness on two-generator recursive presentations and on pairs
of words in `V`; [[sofic-recognition-has-a-pi2-upper-bound]] gives membership
in `Pi^0_2` for both, since the induced presentation of a two-generated
subgroup of `V` is recursive uniformly in the pair.  Complements are
`Sigma^0_2`-complete.
