---
rg: 2
id: hyperlinearity-cannot-see-the-lamp-module-proof
kind: route
title: Transport hyperlinearity across a Haar-preserving conjugacy of dual actions
target: hyperlinearity-cannot-see-the-lamp-module
requires:
  - icc-property-t-not-w-star-superrigid
---

Three steps, of which only the third needs the prerequisite.

1. **Hyperlinearity is a property of the group von Neumann algebra.**  A
   countable group `G` is hyperlinear iff `L(G)` embeds into `R^omega`.  This
   is the standard characterization the corpus already leans on — see the
   closing note of `thom-central-corner-criterion`, and the use
   `U(M) <= U(R^U)` in `invariant-graph-ce-route` and
   `hilbert-embeddable-length-hyperlinearity-proof`.  So an isomorphism
   `L(Gamma_1) ~ L(Gamma_2)` transports hyperlinearity in both directions.

2. **A lamp group's factor is a crossed product by the dual action.**  For
   countable discrete abelian `D`, Fourier transform gives

   ```text
   L(D rtimes_theta H) ~ L(D) rtimes H ~ L^infty(hat D, Haar) rtimes H,
   ```

   and conjugate nonsingular actions have isomorphic crossed products: if `F`
   is a Haar-preserving Borel isomorphism of `hat D` with
   `F alpha_(1,h) F^(-1) = alpha_(2,h)` for all `h`, then `F` induces the
   isomorphism of crossed products.  Only the conjugacy class of the action
   enters; the module structure `theta` enters only through it.

3. **The hypothesis is not vacuous, and non-isomorphic modules satisfy it.**
   `icc-property-t-not-w-star-superrigid` supplies `D`, `H`, and two module
   structures whose dual actions are conjugated by the quadratic shear
   `F(z,y) = (z, y + calR(z))`, while the modules themselves are separated by
   semisimplicity — so far apart that the two groups are not isomorphic.  That
   is exactly a witness for the final sentence of the target.

The negative half of the target — that the transfer does **not** carry
soficity or MF-ness — is not an extra step but the absence of one: step 1 is
available for hyperlinearity because of the `R^omega` characterization, and no
analogue exists for either of the other two, MF-ness being a property of
`C*_r(Gamma)` which a von Neumann isomorphism does not see at all.
