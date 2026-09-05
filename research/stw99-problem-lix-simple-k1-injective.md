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
  - research/artifacts/stw59-factorial-torsion-simple-ah-manuscript-2026-09-05.md
  - research/artifacts/stw59-exact-factorial-component-groups-2026-09-05.md
  - research/artifacts/stw59-exact-arbitrary-cyclic-component-groups-2026-09-05.md
  - research/artifacts/stw59-exact-finite-abelian-component-groups-2026-09-05.md
  - research/artifacts/stw59-finite-abelian-independent-review-2026-09-05.md
  - research/artifacts/stw59-unique-trace-and-matrix-stability-2026-09-05.md
---

**Problem LIX of Schafhauser--Tikuisis--White, arXiv:2506.10902.** Are
all unital simple C\*-algebras `K_1`-injective? The cited problem list
presents this as open. The internally reviewed construction
`stw59-simple-ah-non-k1-injective` gives a negative answer within this
research graph: its simple unital nuclear stably finite AH algebra
has K1=0 and a non-null unitary whose square and first matrix
stabilization are null-homotopic. This graph status records the
accompanying proof, not external peer acceptance or formal verification.

The stronger family in `stw59-simple-ah-factorial-unitary-torsion`
preserves exact order n! for every n>=2, by replacing parity with
factorial Chern divisibility and testing every power by sphere degree.
Taking powers gives examples with every prescribed finite cyclic
component order, still with K1 zero. This strengthens the same LIX
counterexample; it does not calculate an entire component group.
The subsequent theorem `stw59-exact-factorial-unitary-component-groups`
does compute the entire group for this family: U(A^(n))/U0(A^(n))
is Z/(n!). In particular, the original example has component group
exactly Z/2. Its proof uses the one-line gauge fibration and computes
the image of its Euler map exactly.

The further strengthening
`stw59-exact-arbitrary-cyclic-unitary-component-groups` realizes
the entire group U(A_d)/U0(A_d) as Z/d for every d>=2, with K1(A_d)=0.
Its initial base is S2 times CP^(d-1); the Euler image is exactly d Z,
and a signed-zero product formula proves that every twisted connecting
map preserves the component generator. This remains a strengthening
of the same LIX counterexample, with internal review rather than
external peer acceptance or formal verification.

The theorem `stw59-exact-finite-abelian-unitary-component-groups`
now realizes every finite abelian group as the entire component
group of one simple AH algebra with K1 zero. Equal-dimension arm
bases are joined at a point, and rank-zero global K0 classes attain
the Euler generators independently on each arm. Thus the joined
base introduces no relations between the prescribed cyclic factors.
The commuting component generators and their first stabilized
contractions persist through the simple limit. A separate internal
review checks the complete joined-base proof.

The further theorem `stw59-monotracial-matrix-stable-counterexamples`
shows that the nontrivial finite-abelian examples have a unique trace
and stable rank exactly two.
At every matrix size m>=2, their canonical stable maps are isomorphisms
in all homotopy degrees. Thus M2(A_G) is K-stable although its full
unital corner A_G is not K1-injective. The proof uses an explicit
Stiefel stable range and the exact one-half contraction of fiber
traces; it does not compute the higher unstable groups at size one.

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
