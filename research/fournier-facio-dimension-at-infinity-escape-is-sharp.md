---
rg: 2
id: fournier-facio-dimension-at-infinity-escape-is-sharp
kind: claim
title: Exact null-boundary blockization still leaves the dimension-at-infinity survivor
invalidates:
  - fournier-facio-null-boundary-cartanization-closes-overlap
distinct_from:
  fournier-facio-hyperfinite-support-exhaustion-misses-cutoff: That calibration leaves a positive charged boundary at every finite stage; this one produces one fixed finite-block comparison with exactly zero charged boundary.
  fournier-facio-block-dimension-escapes-every-charge-cutoff: That is a necessary law for a Fournier--Facio common-block witness; this proves the law is sharp on an exact singular regular-character model.
  fournier-facio-bounded-block-near-witness-impossible: That excludes a uniform finite block bound for the nonsofic candidate; this example has finite blocks whose sizes escape every cutoff in charge.
---

**ESTABLISHED SHARPNESS CALIBRATION.**  A uniform theorem replacing an
infinite support component by one finite-block comparison modulo the charged
null ideal would still not contradict
`fournier-facio-block-dimension-escapes-every-charge-cutoff`.  There is an
exact singular amenable regular-character representation for which such a
comparison already exists and all of its block dimension lies at infinity.

Let `mu` be any translation-invariant probability charge on `Z`.  Put

```text
d_k=k|k|,
I_k={d_k,...,d_(k+1)-1}                    (k in Z).       (FDIS1)
```

The intervals `I_k` partition `Z`, are finite, and their lengths tend to
infinity as `|k|` tends to infinity.  Let `M` cyclically shift each `I_k`
forward by one.  If `T` is the bilateral shift, then `M` and `T` differ only
at the set `E` of right endpoints of the `I_k`.  This set is a translate of
the signed squares, has upper Banach density zero, and hence

```text
mu(E)=0,
phi_mu((T-M)^*(T-M))=0.                                (FDIS2)
```

The permutation `M` preserves `mu`: its action differs from translation only
on `E`, and the same holds for inverse images of every subset.  Therefore

```text
pi(n)=M^n                                                   (FDIS3)
```

is an exact amenable representation of `Z` for the singular diagonal state
`phi_mu`.  It has regular character.  Indeed the fixed points of `M^n`, for
`n!=0`, lie in cycles whose lengths divide `|n|`; only finitely many `I_k`
have such a length, so their union has `mu`-charge zero.

Finally, for every fixed `m`, only finitely many blocks have size at most
`m`.  Thus

```text
mu(union_{|I_k|<=m} I_k)=0                              (FDIS4)
```

for every finite `m`.  The support graph of `T` is one infinite component,
yet `M` is a single exact charged-null finite-block replacement whose block
sizes escape every cutoff.

Consequently neither hyperfinite exhaustion nor its strongest naive
null-boundary upgrade closes the Fournier--Facio survivor.  A useful
Cartanization theorem would additionally have to produce tight block
dimensions (or a positive-charge bounded stratum), something the invariant
charge alone cannot force.  Otherwise one must obstruct the genuinely
dimension-at-infinity internal matrix dynamics directly.

Proof: `fournier-facio-dimension-at-infinity-sharpness-proof`.
