---
rg: 2
id: nonhyperlinear-sep7-logarithmic-stability
kind: route
title: Extract microscopic logarithmic seeds until the SL5 tuple is corrected
target: sln-z-flexibly-hs-stable
requires:
  - nonhyperlinear-sep7-logarithmic-seed
  - nonhyperlinear-sep7-osgood-extraction
  - moving-subgroup-schreier-correction-has-no-index-loss
artifacts:
  - research/artifacts/nonhyperlinear-sep7-osgood-extraction.md
---

Given the seed hypothesis, set
`epsilon^2=B delta(U)^2 log(e/delta(U)^2)` and take the full spectral
space at this cutoff in Q_(2n). It is nonzero. At small enough defect,
`a=2|S|epsilon^2/kappa^2<=1/2`, so `(MSC14)` of the required
Schreier theorem constructs an exact representation of dimension r
with `r/n<=1/(1-a)` and retained-column error at most

```text
xi<=sqrt(|S|)(1+4/kappa)epsilon.
```

If `r<=n`, its polar coisometry supplies the first alternative in the
Osgood extraction theorem. If `r>n`, its padded polar correction
supplies the second, with squared generator error at most xi squared
and relative padding at most `4|S|epsilon^2/kappa^2`. Hence both
alternatives have squared-modulus bound `psi(t)=K t log(e/t)`, for

```text
K=max(|S|(1+4/kappa)^2 B,4|S|B/kappa^2).
```

The required Osgood theorem proves flexible normalized-HS stability
of SL5, establishing the target with n=5. This plugs into the existing
`non-hyperlinear-from-hnn-over-sln-z` route. Its first-vector hypothesis
is still open, so this route is not an unconditional nonhyperlinear
group construction.
