---
rg: 2
id: zero-one-irs-character-is-normal-dirac
kind: claim
title: An IRS character with only zero-one coefficients is a normal Dirac mass
distinct_from:
  diracization-gap-equals-nonhyperlinear-group: that asks for a quantitative gap surviving an asymptotic Diracization procedure; this is an exact measure-theoretic characterization of an already zero-one IRS character.
  non-cohyperlinear-irs-exists: that supplies a non-CE IRS trace but not a normal subgroup; this proves that removing all of its intermediate coefficients would itself produce the missing quotient group.
  projective-word-law-characterizes-twisted-group-factors: that characterizes arbitrary projective bases of finite factors; this concerns the native fixed-point character of one IRS and yields an untwisted quotient when it is zero-one.
---

**ESTABLISHED.**  Let `mu` be an invariant random subgroup of a countable
group `Gamma`, and write

```text
chi_mu(g)=mu({H:g in H}).                               (ZOI1)
```

If `chi_mu(g) in {0,1}` for every `g`, then there is a normal subgroup
`K normal Gamma` such that

```text
mu=delta_K,             chi_mu=1_K.                     (ZOI2)
```

Indeed put `K={g:chi_mu(g)=1}`.  Countability gives a conull set on which
every member of `K` belongs to `H`, and another conull set on which no member
of `Gamma\K` belongs to `H`.  Hence `H=K` almost surely.  Invariance of `mu`
makes `K` normal.

Consequently every genuinely non-Dirac IRS has a fixed group element with

```text
0 < chi_mu(g) < 1.                                     (ZOI3)
```

Applied to the non-cohyperlinear Manzoor IRS on a free group `F`, this gives
an exact dichotomy.  Either `(ZOI3)` holds, so the native GNS group unitaries
fail the zero-or-scalar projective-word law already at a one-letter
coefficient; or the IRS is `delta_K`, in which case its GNS algebra is
`L(F/K)`.  Non-Connes-embeddability then says directly that `F/K` is a
nonhyperlinear group.  Thus eliminating the intermediate native IRS
coefficients is not a preliminary simplification of the source: it is the
complete group-level breakthrough.

DERIVATION
countable-zero-one-membership-forces-one-subgroup
