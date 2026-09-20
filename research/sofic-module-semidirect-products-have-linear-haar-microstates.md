---
rg: 2
id: sofic-module-semidirect-products-have-linear-haar-microstates
kind: claim
title: Converse of the linear sofic code criterion - a sofic F_p-module semidirect product has linear sofic codes
distinct_from:
  linear-haar-microstates-make-module-semidirect-products-sofic: that is the established direction (codes imply soficity); this asks the converse, which would make the linear-code fence exact.
  abelian-by-virtually-free-groups-are-sofic: that proves soficity over virtually free actors by amalgamation; this asks whether such soficity is always witnessed by LINEAR codes, which that proof does not produce.
  dense-homoclinic-algebraic-actions-are-ce: that is a sufficient condition for CE; this is a structural converse for group soficity.
---

OPEN. Let `Lambda` be a countable group, `A` an `F_p[Lambda]`-module, and
suppose `A semidirect Lambda` is sofic. Does `A` have linear sofic codes over
`Lambda`, in the sense of
[[linear-haar-microstates-make-module-semidirect-products-sofic]]?
Equivalently, when `A` is finitely generated, does
`K = hat A` in `(F_p^m)^Lambda` have linear Haar microstates (LHM) along some
sofic model of `Lambda` for every window?

A positive answer would make the linear-code fence on
[[algebraic-compact-action-envelope-for-non-ce-relation]] lose nothing
against soficity. A negative answer would produce a sofic `A semidirect Lambda`
whose soficity is invisible to every affine-linear model. That would be the
first sign that the SL_3(Z) module search must exploit nonlinear microstates.

## Attempts

- **Positive cases (proved).** (E1)-(E6) of the established direction give
  the converse whenever `A` is:
  - free;
  - over an amenable actor;
  - dense-periodic;
  - dense-homoclinic;
  - a permutation module over a LERF actor;
  - a submodule or directed union of such modules.
- **The obstruction is local-to-global.** Fix `V = Lambda/H`. The universal
  truncated code is
  `U = (direct sum over v of F_p[D]^m) / (C2 relations + local relations R cap F_p[D]^m)`.
  Its (C2) and well-definedness hold by construction, and (C3) is the only
  condition. Without truncation this `U` is the coinvariant module `A_H`,
  and (C3) becomes residual finiteness of `A` (E4). With truncation it is a
  module analogue of LERF, of which (E6) is the permutation case.

  A general module over a non-LERF actor, such as `SL_3(Z)`, can fail this
  for every finite quotient while other sofic models, or non-quotient `V`,
  still work. No argument converts an arbitrary sofic approximation of
  `A semidirect Lambda` into a linear one. Averaging or linearising the
  permutations `Pi(a)` over `F_p` gives only approximate additivity, not the
  exact linearity of `iota_v`.
- **Extraction caveat resolved.** It had been feared that the converse at
  `Lambda = F` free would force every group to be sofic, via codes for
  `F_p[F/N]`. (E6) shows that such codes exist for every `N`, by M. Hall's
  theorem, so that fear is void. Over free actors the converse is open only
  for non-permutation modules. There `A semidirect F` is always sofic by
  [[abelian-by-virtually-free-groups-are-sofic]], so a counterexample would
  have to live there, or over a non-LERF actor.
- **Test case.** Finitely presented modules over virtually free actors are
  residually finite by [[finite-type-linear-vfree-envelope-is-residually-finite]].
  Via coinvariants they should then fall under (E4), though that link is not
  checked here.

  So the first real test is the cyclic, recursively presented, nonresidual
  `F_p[F]`-module of [[nonresidual-linear-module-can-give-a-sofic-envelope]].
  Its semidirect product is sofic. Does it have linear codes, for example
  through a truncated universal code on some finite quotient of `F`? Nothing
  is computed yet.
