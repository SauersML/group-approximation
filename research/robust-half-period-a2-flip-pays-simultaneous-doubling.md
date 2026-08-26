---
rg: 2
id: robust-half-period-a2-flip-pays-simultaneous-doubling
kind: claim
title: Four half-period A2 flip residuals robustly pay simultaneous deep-root doubling
distinct_from:
  same-reservoir-weyl-pair-has-fixed-depth-doubling-gap: that assumes an exact central primitive commutator and obtains an exact fixed-depth floor; this replaces centrality and primitive spectral exactness by four explicit finite-word residuals.
  involutory-steinberg-simple-root-forces-long-root-involution: that closes the bottom exponent-two stratum using one Steinberg commutator; this treats every fixed deeper two-power stratum after a common two-root carrier has been selected.
  cyclic-doubling-matching-hides-full-deep-root-budget: that gives a vanishing-cost matching for one cyclic root clock; this proves that one common conjugator cannot match two transverse roots when the half-period commutator changes sign.
  arithmetic-hexagon-decoding-or-conductor-leakage: that must extract common carriers across the closed six-chamber gallery; this is the dimension-free analytic inequality available immediately after one primitive shared A2 carrier has been authenticated.
---

Let `N>=2`, `d=2^N`, and `m=d/2`.  For matrix unitaries `P,Q,V` put

```text
epsilon_P=||V P V^*-P^2||_2,
epsilon_Q=||V Q V^*-Q^2||_2.                            (RHF1)
```

Define four finite-word half-period residuals

```text
alpha_P=||[P,Q^m]+I||_2,
beta_P =||[P^2,(Q^2)^m]-I||_2,
alpha_Q=||[P^m,Q]+I||_2,
beta_Q =||[(P^2)^m,Q^2]-I||_2,
Delta=alpha_P+beta_P+alpha_Q+beta_Q.                    (RHF2)
```

Then, in every matrix dimension,

```text
epsilon_P+m epsilon_Q >= 1-(alpha_P+beta_P)/2,
m epsilon_P+epsilon_Q >= 1-(alpha_Q+beta_Q)/2.          (RHF3)
```

Consequently

```text
epsilon_P+epsilon_Q
 >= (2-Delta/2)_+/(m+1),

epsilon_P^2+epsilon_Q^2
 >= 2(1-Delta/4)_+^2/(m+1)^2.                          (RHF4)
```

All constants depend only on the fixed decoded depth `N`, never on ambient
dimension or representation multiplicity.  When `Z=[P,Q]` is central and
`Z^m=-I`, the two `alpha` residuals vanish.  The doubled commutator has
half-period `+I`, so the two `beta` residuals vanish as well; `(RHF4)` then
recovers exactly the floor of
`same-reservoir-weyl-pair-has-fixed-depth-doubling-gap`.

The formulation in `(RHF2)` is more useful for approximate arithmetic root
packets.  It does not require exact spectral projections, an exact finite
Heisenberg representation, or prior exactification of its center.  The four
terms are literal words of length depending only on `N`, so on a fixed-depth
band they are controlled by the corresponding shared-root Steinberg and
power relators by ordinary telescoping.

## Scope

This closes the analytic **post-selection** part of the first deep
two-primary A2 stratum.  Independent cyclic clocks evade it by failing at
least one half-period commutator flip, while a genuine primitive common
Weyl reservoir pays simultaneous doubling.  It does not select that common
reservoir.  The remaining hexagon problem is still to show that the two
transverse root operators and their half-period words occupy positive mass
on the same carrier rather than on separately matched rectangular
multiplicity spaces.



