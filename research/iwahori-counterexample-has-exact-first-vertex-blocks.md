---
rg: 2
id: iwahori-counterexample-has-exact-first-vertex-blocks
kind: claim
title: An Iwahori transfer counterexample has two exact positive-density first-vertex representations
distinct_from:
  iwahori-transfer-failure-reduces-to-two-block-projection: that produces an almost-reducing projection; this rounds the first modular vertex to an exact direct sum while retaining the failed second-vertex commutator.
  iwahori-transfer-failure-has-two-positive-density-blocks: that supplies the uniform rank lower bound; this consumes that bound and stability of SL2(Z) to remove the first-vertex approximation.
---

If `iwahori-unitary-commutant-transfer` fails, then after passing to a
subsequence and perturbing the first vertex by `o(1)` in normalized HS norm,
the witnesses may be chosen so that

```text
pi_(n,+)=alpha_(n,0) directSum alpha_(n,1),           (EFB1)
P_n=1 directSum 0,                                   (EFB2)
```

where `alpha_(n,0),alpha_(n,1)` are exact representations of `SL_2(Z)` and
both block dimensions are at least `c d_n` for one `c>0`.  The Iwahori edge
defect still tends to zero, while a commutator of `P_n` with the second
vertex stays bounded below.

Indeed, first use
`iwahori-transfer-failure-reduces-to-two-block-projection` and
`iwahori-transfer-failure-has-two-positive-density-blocks`.  Then apply
`stable-representation-block-rounding` to the exact first vertex, using
`sl2-z-same-dimension-hs-stable`.  The perturbation is vanishing and hence
does not change either the vanishing edge defect or the positive lower bound
on the selected second-vertex commutator.

Thus the unresolved phenomenon is not an approximate decomposition of the
first modular representation.  It is positive-density **extension mixing**:
the second exact modular vertex almost matches the direct-sum Iwahori
restriction of two honest first-vertex representations while failing to
preserve their block projection.
