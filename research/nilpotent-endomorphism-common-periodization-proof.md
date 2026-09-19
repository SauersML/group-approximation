---
rg: 2
id: nilpotent-endomorphism-common-periodization-proof
kind: route
title: Use Hirsch rank and one pro-p Frattini quotient for every nilpotent branch
target: nilpotent-endomorphism-families-have-periodizations
requires: []
artifacts:
  - research/artifacts/nilpotent-endomorphism-common-periodization-proof.md
  - research/artifacts/free-full-h1-endomorphism-common-periodization-proof.md
---

For an injective endomorphism `phi_i` of the finitely generated torsion-free
nilpotent group `Gamma`, the image is isomorphic to `Gamma` and hence has the
same Hirsch length.  A subgroup of a finitely generated nilpotent group has
full Hirsch length exactly when it has finite index.  Therefore
`phi_i(Gamma)` has finite index, and its image in `Gamma_ab` has finite index.
The induced map on the free part of `Gamma_ab` consequently has nonzero
determinant.

Choose a prime `p` dividing neither the order of the torsion subgroup of
`Gamma_ab` nor any of those finitely many determinants.  Gruenberg's
residual-`p` theorem embeds `Gamma` in its pro-`p` completion `P`.  Every
`phi_i` extends continuously, and the prime choice makes its map on

```text
P/Phi(P) = H_1(Gamma;F_p)
```

invertible.  The pro-`p` Burnside basis argument makes the extension
surjective, and Hopficity of finitely generated profinite groups makes it an
automorphism.

Choose an open normal subgroup `U` of `P` which omits the marked element `y`,
and intersect all open subgroups of index at most `[P:U]`.  There are only
finitely many, so their intersection `C` is open; it is characteristic and
contained in `U`.  Thus `Q=P/C` is a finite `p`-group with `q(y)!=1`, and
every extended `phi_i` descends to an automorphism of `Q`.  Sending each HNN
letter to that automorphism gives the finite marked semidirect-product
quotient asserted in the claim.

The first artifact verifies the nilpotent/Hirsch and mod-`p` inputs.  The
second contains the self-contained Frattini, Hopficity, bounded-index, and
characteristic-quotient arguments reused here.
