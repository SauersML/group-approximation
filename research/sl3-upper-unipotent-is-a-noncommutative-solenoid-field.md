---
rg: 2
id: sl3-upper-unipotent-is-a-noncommutative-solenoid-field
kind: claim
title: The SL3 upper-unipotent carrier is a field of noncommutative solenoids, not a joint three-solenoid system
invalidates:
  - sl3-carrier-rank-two-solenoid-action-proof
distinct_from:
  heisenberg-solenoid-trace-torsion-dichotomy: that classifies traces fiberwise and proves the torsion criterion; this records the exact correction to the false abelian SNAG model of the full SL3 upper-unipotent carrier and its consequence for the diagonal action.
  far-sector-is-solenoid-measure-rigidity: that concerns a genuinely abelian rank-one root carrier; this identifies why the corresponding classical measure model does not extend to the three positive roots of SL3.
---

Let `R=Z[1/p]`, let

```text
N=<a(x)=e_12(x), b(y)=e_23(y), c(z)=e_13(z): x,y,z in R>
```

be the upper-unipotent subgroup of `SL_3(R)`, and let `D iso Z^2` be the
diagonal `p`-power subgroup.  Then:

1. `N` is the nonabelian Heisenberg group, with
   `[a(x),b(y)]=c(xy)` and center `c(R)`.  In particular, `N` is not
   `R^3`, there is no joint projection-valued measure for its three root
   coordinates, and states of `C*(N)` are not measures on `hat(R)^3`.
2. The valid spectral decomposition is only over the central solenoid
   `S_p=hat(R)`.  At central character `zeta`, the fiber is the twisted
   group algebra

   ```text
   A_zeta=C*(R^2,sigma_zeta),
   sigma_zeta((x,y),(x',y'))=zeta(-x'y),
   ```

   a Latremoliere--Packer noncommutative solenoid.  The `D`-action
   transports `A_zeta` to the fiber obtained by scaling `zeta`; it is not
   a classical rank-two action on one joint three-solenoid.
3. For the canonical trace of `N`, the central measure is Haar on `S_p`.
   Haar gives zero mass to the countable torsion subgroup, and almost every
   fiber has its unique canonical trace.  Thus the regular restriction is
   still pinned exactly, but as a noncommutative direct integral, not as a
   joint Haar probability measure on `S_p^3`.

Consequently classical higher-rank algebraic measure rigidity cannot be
applied directly to the full upper-unipotent restriction.  Any surviving
SL3 transfer argument must retain the Heisenberg multiplier/multiplicity
fibers (or pass to the center or abelianization, where classical SNAG is
valid).  This is exactly the multiplicity gauge that remains visible in the
noncorrectable projective-leak sector.

