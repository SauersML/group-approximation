---
rg: 2
id: stw27-low-rank-soft-divider-rounding
kind: claim
title: A low-rank homogeneous almost divider is compact, with sharp threshold n(n+1)
distinct_from:
  stw27-coordinate-euler-slack-obstructs-compact-dividers: that claim obstructs projection dividers by characteristic classes; this claim gives the exact rank window in which every possibly soft divider is automatically a projection, and shows why that rounding stops at the boundary.
artifacts:
  - research/artifacts/stw27-soft-divider-hinge-audit-2026-08-30.md
---

Let `X` be compact, let `E` be a complex vector bundle of constant positive
rank `M` over `X`, and put `x=[E] in Cu(C(X))`.  Fix `n>=2`.  If

```text
M < n(n+1)
```

and `y in Cu(C(X))` satisfies

```text
n y <= x <= (n+1)y,                                  (1)
```

then `y` is compact: it is the class of a finite-rank vector bundle `F`, and
`(1)` is the vector-bundle sandwich

```text
nF is a subbundle of E,
E is a subbundle of (n+1)F.
```

The threshold is sharp for forcing the given witness to be compact.  At
`M=n(n+1)`, take `X=[0,1]` and

```text
y = [C(X)^n direct_sum C_0((0,1])].
```

Then `n y <= M[1] <= (n+1)y`, but `y` is noncompact because its fibre rank
jumps from `n` at zero to `n+1` away from zero.

Combining the first assertion with
`stw27-coordinate-euler-slack-obstructs-compact-dividers` gives a full,
soft-inclusive finite-block obstruction.  For prime `ell`, if

```text
E = theta_s direct_sum direct_sum_i L_i^(direct_sum t_i),
M < ell(ell+1),
(ell+1) cardinality{i : ell does not divide t_i} > M,
```

then there is no `y in Cu(C((S^2)^N))` satisfying
`ell y <= [E] <= (ell+1)y`.
