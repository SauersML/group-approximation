---
rg: 2
id: pcp-subroutes-share-lin-barrier-proof
kind: route
title: Locate the coRE crux's area-beating mechanism inside the RE compiler's target
target: pcp-subroutes-to-both-hs-dehn-orientations-share-lin-barrier
requires: []
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Structural derivation, from the contents of the cited nodes.

* The coRE crux `unsolvable-word-problem-group-with-computable-hs-dehn-modulus`
  records, in its Attempts, that every non-PCP source of length control it
  tried tracks the Dehn function or fails to produce an unsolvable word
  problem, and that the Taller--Vidick sub-route gives linear length control
  for a length-one word of unbounded area on the `J = -1` sector.

* That sub-route controls the marked word only under `J = 1` on the
  completeness side; `J != 1` there is closed immediately by
  `perfect-lcs-gap-implies-nonhyperlinear`.  A computable binary-`LIN` family
  with `J = 1` on halting inputs and a constant nonhalting matrix gap is the
  statement of `perfect-completeness-constant-soundness-lcs-compiler`
  (`(PC1)` and `(PC2)`).  So the coRE crux's PCP sub-route requires that RE
  target.

* `perfect-completeness-constant-soundness-lcs-compiler` records that the
  published perfect-gap CSP families are nonaffine
  (`culf-mastel-oracular-2csp-perfect-gap-family`) and that pp-definability
  from `LIN` forces affine relations, so the perfect gap does not cross into
  `LIN`; `selector-gated-equality-is-not-affine-pp-definable` is the fence.

The three points give the claim: the currently-live PCP attacks on both
orientations are blocked at the one affine-`LIN` barrier.  The route is a
reading of the existing nodes, not a new construction, and it establishes
only the structural statement, not either existence crux.
