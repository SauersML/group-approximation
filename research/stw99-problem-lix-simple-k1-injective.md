---
rg: 2
id: stw99-problem-lix-simple-k1-injective
kind: claim
title: Unital simple C*-algebras are K1-injective (STW Problem LIX)
root: true
refuted_by:
  - stw59-simple-ah-non-k1-injective
distinct_from:
  stw99-problem-lxi-properly-infinite-k1-injective: that asks K1-injectivity from proper infiniteness without simplicity; this asks it from simplicity without any regularity, and Villadsen's Crelle examples already kill the surjectivity analogue here.
artifacts:
  - research/artifacts/stw99-k1-kk-cluster-2026-08-30.md
  - research/artifacts/stw59-twisted-torsion-test-2026-09-05.md
  - research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md
---

**Problem LIX of Schafhauser--Tikuisis--White, arXiv:2506.10902.** Are
all unital simple C\*-algebras `K_1`-injective? The cited problem list
presents this as open. The internally reviewed construction
`stw59-simple-ah-non-k1-injective` gives a negative answer within this
research graph: its simple unital nuclear stably finite AH algebra
has K1=0 and a non-null unitary whose square and first matrix
stabilization are null-homotopic. This graph status records the
accompanying proof, not external peer acceptance or formal verification.

## Attempts

* The ordinary diagonal coordinate-duplication version of the unstable
  torsion attack is excluded. Seth's Theorem A and Corollary 3.10
  (arXiv:2512.04780v1) give K-stability for every simple unital
  infinite-dimensional diagonal AH algebra, even after tensoring
  with any C*-algebra. Elliott--Ho--Toms stable rank one already
  excludes K1-injectivity counterexamples in this simple diagonal
  class. The previous statement that no literature result blocks
  this route was too broad.
* The twisted-corner obstruction is now computed and made persistent.
  For Y a product of CP^(d_j) and H the direct sum of d_j tautological
  lines from each factor, F direct-sum H is not isomorphic to
  C2 direct-sum H. The proof uses an odd Euler number versus an even
  mapping-torus Chern number, including all gauge automorphisms.
  The resulting order-two unitary survives the explicit simple twisted
  inductive system. See `stw59-simple-ah-non-k1-injective` and the
  complete manuscript. The older finite-test artifact records the
  exact quotient reduction; its survival question is now settled.
  The particular subgroup D inside Z/24 is not identified by this
  argument and is not needed for the counterexample.
