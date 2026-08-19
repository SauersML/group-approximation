---
rg: 2
id: property-tt-mod-t-rigidity-for-elementary-groups
kind: claim
title: Property (TT) modulo T for elementary groups over finite free characteristic-two presentations
distinct_from:
  elementary-group-property-t-over-free-algebras: That is property (T) itself, a spectral-gap statement about unitary representations; this is the strictly stronger quasi-cocycle rigidity (TT)/T, and it carries division and diagonal-class hypotheses that (T) does not.
  universal-leavitt-el4-nonsofic: That is a soficity statement; this file's surface deliberately contains no nonsoficity input, so that the rigidity theorem keeps an independent dependency closure.
artifacts:
  - GroupApproximation/PropertyTT/PaperStatements.lean
  - GroupApproximation/PropertyTT/FiniteTypeLeavittTT.lean
  - property_tt_leavitt.tex
---

ESTABLISHED.  `PropertyTT/PaperStatements` is the rigidity paper's public
surface -- each declaration carries the exact hypotheses and conclusion of a
numbered manuscript theorem.  The synthesis statements:

* `finiteFreeQuotient_rankFour_hasTTmodT` -- for a nontrivial ring `R` that is
  a surjective image of a finite free `ZMod 2`-algebra and carries a binary
  Leavitt family, single-sandwich division and a trivial elementary diagonal
  class, `EL_4(R)` has `(TT)/T`;
* `finiteFreeQuotient_elementaryGroup_hasTTmodT` -- the same four hypotheses
  give `(TT)/T` in every elementary rank at least two, with
  `finiteType_elementaryGroup_hasTTmodT` the same statement in ordinary
  language (finite type over `ZMod 2`, the free surjection built rather than
  assumed);
* `kazhdan_normalizedSet_globalization` -- relative `(TT)/T` on a generating
  set that a subgroup normalizes globalizes to relative `(TT)/T` for that
  subgroup, given property `(T)`;
* `quasiCocycle_list_product_bound` -- the empty-list-safe product estimate
  `‖b(∏ l)‖ ≤ |l|·C + (|l|+1)·D` that bounded generation runs on.

The algebraic half of the hypothesis list is
[[coordinate-block-factorization-under-single-sandwich]], stated for any
single-sandwich ring; the hypothesis-free specialization, where all four
hypotheses are discharged and the group is named, is
[[binary-leavitt-unit-group-has-tt-mod-t]].

## Why the surface is kept free of soficity

Deliberately: the combined nonsofic corollary lives in a separate endpoint so
that the rigidity theorem has an independent dependency closure; that endpoint
is `PropertyTT/NonsoficCorollary`, recorded at
[[binary-leavitt-unit-group-has-tt-mod-t]]. That is worth
recording because it is the opposite of how the nonsoficity endpoint is
usually described -- the rigidity results do not need it, and a reader
checking `(TT)/T` should not have to trust the compression criterion.
