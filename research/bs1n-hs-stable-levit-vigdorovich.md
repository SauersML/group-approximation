---
rg: 2
id: bs1n-hs-stable-levit-vigdorovich
kind: claim
title: BS(1,n) is Hilbert--Schmidt stable in the same dimension, and every trace of BS(1,2) whose restriction to Z[1/2] is the Dirac trace is the regular trace
distinct_from:
  bs1n-rq-padded-opnorm-stability: that is Willett's operator-norm R_q-stability with an uncontrolled padding; this is the normalized Hilbert--Schmidt statement with no padding, plus the Bekka--de la Harpe vanishing lemma.
  bs14-hs-stability-does-not-supply-relative-op-basin: that shows HS-stability of BS(1,4) gives no operator-norm basin; this only imports the HS-stability theorem itself as a citable prerequisite.
---

**ESTABLISHED** by `bs1n-hs-stable-levit-vigdorovich-citation` (verbatim import,
not reproved).

1. (Levit--Vigdorovich, Corollary D(3).)  For every nonzero integer `n`,
   `BS(1,n)` is Hilbert--Schmidt stable: for every asymptotic homomorphism
   `f_k : BS(1,n) -> U(k)` in the normalized Hilbert--Schmidt metric there are
   homomorphisms `phi_k : BS(1,n) -> U(k)`, *in the same dimension `k`*, with
   `d_HS(f_k(g), phi_k(g)) -> 0` for every `g`.
2. (Bekka--de la Harpe, as Lemma 3.5 of the same paper.)  If `N` is an abelian
   normal subgroup of `G` and `phi` is a trace on `G` whose restriction to `N`
   has Fourier measure `mu_phi` on `hat N`, then `phi(g) = 0` for every `g`
   acting `mu_phi`-essentially freely on `hat N`.

**Corollary used downstream (elementary from 2).**  Let
`G = BS(1,2) = Z[1/2] rtimes Z` with `t a t^(-1) = a^2`.  If a trace `phi` on
`G` has `phi(a^q) = 0` for every `q` in `Z[1/2] \ {0}`, then `phi` is the
regular trace `delta_e`.

*Proof.*  `mu_phi` is Haar measure on the solenoid `Sigma_2 = hat(Z[1/2])`,
because its Fourier coefficients are `delta`.  Every element of `G` is
`a^q t^k`.  For `k = 0` the hypothesis applies.  For `k != 0`, conjugation by
`a^q t^k` acts on `hat N` as `t^k` does, since `N` is abelian, and that action
is `chi -> chi(2^k .)`.  Its fixed points are the characters trivial on
`(2^k - 1) Z[1/2]`.  This subgroup has finite index, because `2^k - 1` is a
unit of `Z[1/2]` times an odd integer `m`, and `Z[1/2]/m Z[1/2] = Z/m`.  So the
fixed set is finite, hence Haar-null, and `a^q t^k` acts essentially freely.
Item 2 then gives `phi(a^q t^k) = 0`.  QED.
