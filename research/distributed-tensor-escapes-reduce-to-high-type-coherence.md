---
rg: 2
id: distributed-tensor-escapes-reduce-to-high-type-coherence
kind: claim
title: Distributed tensor countermodels reduce to high type or approximate-projective coherence
distinct_from:
  tensor-products-cannot-cancel-noncentral-hs-defect: that proves the analytic scalarization inequality; this combines it with dense stopping support and bounded-type rounding to classify the surviving tensor-network escapes.
  operator-tail-contraction-misses-uniform-diffuse-matching: that exhibits a scalar profile invisible to tail contraction; this shows why the obvious tensor realizations of that profile do not work.
  bounded-type-noncentral-code-sectors-round-uniformly: that localizes an arbitrary countermodel to large irreducible type; this additionally rules out distributed cancellation as the source of that type.
---

For the all-local-dual DELL​M presentation, every factorwise-exact
nonabelian tensor factor has dense commutation support.  If

```text
A_f={i:[Q_i^(f),Q_j^(f)]!=0 for some j},
```

then `|A_f|>=alpha L`, and
`unique-neighbor-ldpc-checks-force-dense-noncommutation` gives at least

```text
alpha^2 L^2                                                  (DTE1)
```

ordered noncommuting pairs in that factor.  Thus a factor cannot implement
a sparse edge, star, or moving two-site corner while respecting every local
face.

The remaining elementary tensor escapes are also fenced:

1. bounded coordinate participation and bounded bond type imply uniformly
   bounded assembled type, hence rounding, by
   `bounded-participation-tensor-networks-are-not-diffuse-far`;
2. arbitrary cross-factor cancellation of parity or commutator words has
   vanishing total noncentral part by
   `tensor-products-cannot-cancel-noncentral-hs-defect`;
3. arbitrary central direct sums with tight irreducible-type distribution
   round by `bounded-type-noncentral-code-sectors-round-uniformly`.

Consequently a tensor-based diffuse far sequence must place nonvanishing
trace on intrinsically unbounded-type factors and must exploit instability
in converting their approximately scalar relative commutators into one
coherent projective phase system.  Alternatively, it must abandon
factorwise face satisfaction and arrange approximate relations through an
unbounded-overlap cancellation whose noncentral part still obeys `(TSC2)`.

This is a reduction, not an exclusion of the final high-type coherence
regime.  In particular, support density `(DTE1)` gives no lower normalized-HS
scale for its nonzero commutators.
