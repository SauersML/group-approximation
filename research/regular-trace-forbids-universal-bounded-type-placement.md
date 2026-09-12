---
rg: 2
id: regular-trace-forbids-universal-bounded-type-placement
kind: claim
title: The regular trace forbids universal placement of a finite packet carrier in bounded Kazhdan types
distinct_from:
  finite-normalizer-covariance-density-no-go: that constructs finite semidirect quotient representations for automorphism covariance; this rules out every representation-universal bounded-type placement directly in the regular representation, regardless of the covariance syntax.
  fd-invisible-anchor-does-not-localize-bcs-consistency: that shows exact finite-dimensional invisibility does not imply localized HS collapse; this shows why exact all-representation covariance cannot supply the desired bounded-type localization while preserving the packet and Kazhdan subgroup.
  canonical-marked-corner-kazhdan-density-vanishes: that is the eventual microstate contradiction; this separates that necessarily matrix-only contradiction from impossible universal C-star containment.
---

Let `G` contain an infinite property-`(T)` subgroup `Lambda` and a finite
packet subgroup `B`.  Let `0!=z=z*=z^2 in C[B]` and let
`p_<=K in C*_max(Lambda)` be the bounded-type central projection of
`kazhdan-bounded-types-form-central-summand`, both viewed in
`C*_max(G)`.  Then

```text
lambda_G(p_<=K)=0,                 lambda_G(z)!=0,       (RUP1)
tau_G(p_<=K)=0,                    tau_G(z)>0.            (RUP2)
```

Consequently none of the following can hold universally in unitary
representations of `G`:

```text
z=z p_<=K,                 z<=p_<=K,
tr(z)<=C tr(p_<=K) for every tracial representation.     (RUP3)
```

The same conclusion holds for a nonzero marked packet projection such as
`z=e_-P_f` whenever the finite marked packet embeds in `G`.

Therefore an ordinary coefficient-covariance cell cannot prove `(PCD1)` by
an exact representation-theoretic inclusion of the forbidden packet carrier
in bounded old-`Lambda` types: the regular representation of the completed
group would violate that inclusion.  If the packet and `Lambda` remain
embedded, the desired promotion must be genuinely **finite-matrix-only**--a
normalized-HS instability statement which fails in the regular
representation.  Together with
`commutant-density-forces-bounded-type-mass`, this shows that `(PCD1)` is not
a missing algebraic placement lemma; it is already the analytic
nonhyperlinearity gate in bounded-type form.

