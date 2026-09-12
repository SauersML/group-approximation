---
rg: 2
id: nonhyperlinear-sep7-logarithmic-seed
kind: claim
title: Every small-defect SL5 tuple has a logarithmic universal-host spectral seed
artifacts:
  - research/artifacts/nonhyperlinear-sep7-osgood-extraction.md
distinct_from:
  moving-subgroup-schreier-correction-has-no-index-loss: that constructs corrections from supplied spectral data and states a sufficient linear seed estimate; this is the unresolved existence of one spectral vector at the larger logarithmic cutoff for every tuple.
  sln-z-flexibly-hs-stable: that is the flexible-stability conclusion for some higher-rank integral lattice; this is a dimension-uniform quantitative first-vector statement for SL5 in its specified finite universal host.
---

Fix the symmetric elementary presentation and Kazhdan generating set
S of `G=SL_5(Z)` used in
`moving-subgroup-schreier-correction-has-no-index-loss`. Let `Q_(2n)`
be its universal finite quotient containing every irreducible type
of dimension at most `2n`. For an inverse-compatible tuple in U(n),
write `delta(U)` for its maximum normalized-HS defining-relator
defect, and on `Hom(C^n,ell^2(Q_(2n)))` set

```text
D_s(T)=lambda_(Q_(2n))(s)T-TU_s,
Delta_U=(1/|S|)sum_s D_s*D_s.
```

There exist `B>0` and `delta_*>0`, independent of n and the tuple,
such that every `0<delta(U)<delta_*` satisfies

```text
min Spec Delta_U <=B delta(U)^2 log(e/delta(U)^2).
```

This claim is open. It requires one vector and no positive normalized
spectral count.

## Attempts

The existing linear seed bound `(MSC19)` would imply this claim, since
`log(e/delta^2)>=1` at small defect, but that uniform linear bound is
itself unproved; no converse is asserted. The curved Hodge heat theorem
improves a supplied low-energy contraction and transfers supplied
positive fixed-cutoff spectral mass to smaller cutoffs. Neither argument
creates a first vector for an arbitrary tuple with no such supplied
mass. The irreducible rigidity theorem closes the supplied-target case
when its dimension is at least the input dimension; it does not supply
that target. Quadratic curvature support likewise supplies no
finite-dimensional coefficient seed. Thus the logarithmic allowance
weakens the quantitative input needed for finite extraction, while the
existence of that input remains the direct arithmetic boundary.
