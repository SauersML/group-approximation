---
rg: 2
id: affine-halt-support-to-nonhyperlinear-proof
kind: route
title: Push the affine proof section through cap profiles and the native sign fixed point
target: affine-halt-support-and-pcpp-section-close-nonhyperlinear-chain
requires:
  - culf-mastel-oracular-2csp-perfect-gap-family
  - dfnqxy-answer-reduction-does-not-preserve-affine-safe-support
  - boolean-relations-have-affine-complete-rstar-pp-gadgets
  - cm-empty-replacement-is-fano-cap-safe
  - finite-lcs-product-sign-is-exact-or
  - re-oriented-lcs-compiler-gives-nonhyperlinear-group
---

On each affine hull, compose the affine perfect-proof section with the linear
Hadamard encoding and each linear view restriction.  Perfectness puts the
resulting affine image inside the `Verify` predicate, so every observed
support is affine-safe.  The non-`Verify` rows are already affine-safe.

Apply the affine-complete truth-table `R_*` gadget to every source predicate.
Its exact visible projection preserves NONHALT ultraproduct soundness, while
its cap-valued witness section extends the HALT model.  Enumerate the seven
cap choices at each target context and turn each profile into its affine LCS
branch.  The product-sign OR combines this finite menu: a HALT model makes
the standard sign negative, and a negative marked ultraproduct model on the
NONHALT side decodes on a nonzero selector corner to one source model.

This is the RE-oriented finite LCS compiler.  The proof-search fixed point
keeps its central sign on a nonhalting index.  Hyperlinearity would give
canonical microstates whose central negative corner has asymptotic trace
one half, hence a perfect Connes-embeddable model of the nonhalting LCS.  The
source gap forbids that.  The solution group at the fixed point is already
finitely presented.
