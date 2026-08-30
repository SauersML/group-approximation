---
rg: 2
id: stw99-lxvi-car-forces-unbounded-cu-perforation
kind: claim
title: A finite CAR projection in a simple infinite algebra forces unbounded Cu perforation certificates
distinct_from:
  stw99-lxvi-z-stability-forbids-mixed-projections: that derives a contradiction from the almost unperforation supplied by Z-stability; this extracts an explicit unbounded family of almost-unperforation failures from the CAR dyadic tower without any regularity hypothesis.
  stw99-lxvi-car-corner-forces-unbounded-stability-indices: that measures how long finite matrix amplifications remain finite; this produces intrinsic order-theoretic perforation certificates in the Cuntz semigroup.
  stw99-lxvi-k0-dyadic-divisibility-obstruction: that is a necessary K0 divisibility test; this proves severe Cu comparison failure even when all of the required dyadic K0 roots exist.
artifacts:
  - research/artifacts/stw99-lxvi-unbounded-cu-perforation-audit-2026-08-30.md
---

Let `B` be a simple unital C\*-algebra containing an infinite projection, and
let `D` be a unital copy of the CAR algebra in `B`.  If `D` contains a
nonzero projection `p` which is finite in `B`, then `Cu(B)` has
almost-unperforation failures with unbounded comparison coefficients.

Precisely, for every `n>=1` there are a nonzero finite projection `q_n<=p`
and an integer `m_n>2^n` such that, with

```text
u=[1_B],          x_n=[q_n] in Cu(B),
```

one has

```text
(m_n+1)u = u = m_n x_n,          but          u not<=x_n.
```

The coefficients satisfy `m_n -> infinity`.  In particular, the ambient
algebra in any solution of STW Problem LXVI must have a Cuntz semigroup
which is not almost unperforated.  This obstruction uses neither
separability nor nuclearity, and it is strictly stronger than merely saying
that an LXVI witness is not Z-stable.
