---
rg: 2
id: a5-arithmetic-shell-envelope-is-finitely-presented
kind: claim
root: true
title: The specified bijective-base A5 free-product shell envelope is finitely presented
distinct_from:
  perfect-decidable-inputs-have-fp-shell-envelopes: that allows an arbitrary suitable enumeration for every perfect input; this fixes one explicit enumeration of one perfect input. Failure of this benchmark would not refute the existential universal route.
artifacts:
  - research/artifacts/boone-higman-arithmetic-shell-benchmark-2026-09-08.md
  - research/artifacts/boone-higman-free-shift-presentation-obstruction-2026-09-08.md
  - research/artifacts/boone-higman-arithmetic-odometer-model-2026-09-08.md
  - research/artifacts/boone-higman-terminated-digit-resolution-2026-09-08.md
---

The particular E_nu defined in
`a5-free-product-has-simple-arithmetic-shell-envelope` is finitely
presented. This is OPEN.

This is an independent finite-presentation benchmark. Resolving this
one prescribed envelope would not by itself settle the universal
perfect-input shell-envelope assertion.

## Attempts

Its exact arithmetic action, faithful input embedding, simplicity,
finite generation, and decidable word problem are established by
the linked claim. These provide a concrete group for presentation
work beyond the virtually cyclic positive control. They do not
prove that the recursively enumerable set of true relations has
a finite normal generating subset. The deterministic finite-state
route is unavailable for this action. No finite presentation or
obstruction to finite presentation has been supplied.

The free-near-shift obstruction does not apply to this action:
`arithmetic-near-shift-actions-have-mixed-relations` gives the exact
relation [lambda_a*s^118*lambda_a^-1,s^6962]=1 for every nonidentity
factor element a. This proves its near group is not P*<s>, but
does not establish finite presentation of either group.

The near group R_nu and the full germ group Q now embed in
explicit finitely presented odometer ambient groups, by
`a5-arithmetic-germs-embed-in-fp-odometer-host`. Neither equality
with those ambient groups nor finite presentation of the subgroups
has been proved. The construction is not an embedding of E_nu.
More precisely, `a5-arithmetic-near-group-obeys-parity-charge-constraint`
excludes equality with the full odometer ambient B and places R_nu
in its index-two parity-charge subgroup B_0. Equality with B_0,
or finite index in B_0, is unresolved.

The separate claim
`a5-arithmetic-shell-envelope-embeds-in-fp-simple-group` now gives
a finitely presented simple OVERGROUP of the entire envelope,
via a terminated-digit action and a contracting RSG. It preserves
the neighborhood kernels. This does not prove the present claim
that E_nu itself is finitely presented.
