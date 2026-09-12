---
rg: 2
id: sl3z-cstar-simple-not-acylindrically-hyperbolic
kind: claim
title: SL3(Z) is C*-simple but not acylindrically hyperbolic
invalidates: [agkp-selfless-instances-of-xc]
distinct_from:
  stw99-all-cstar-simple-groups-acyl-hyp-rd: that is the universal statement over all C*-simple groups; this is the single counterexample refuting it.
  agkp-acylindrically-hyperbolic-rd-groups-selfless: that is a theorem about groups inside AGKP's hypotheses; this exhibits a C*-simple group outside them.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw91-selfless-group-frontier-2026-08-30.md
---

`SL₃(ℤ)` has simple reduced C*-algebra (Bekka--Cowling--de la Harpe, *Some
groups whose reduced C*-algebra is simple*, Publ. Math. IHÉS 80 (1994)), and it
is not acylindrically hyperbolic: acylindrically hyperbolic groups are
SQ-universal (Dahmani--Guirardel--Osin, Mem. AMS 245 (2017), Theorem 2.33 as
recorded in Osin, *Acylindrically hyperbolic groups*, Trans. AMS 368 (2016),
Theorem 1.4), so they have uncountably many normal subgroups, while by the
Margulis normal subgroup theorem every normal subgroup of `SL₃(ℤ)` is finite or
of finite index, so there are only countably many.

**Established (literature).**  It refutes
`stw99-all-cstar-simple-groups-acyl-hyp-rd` and so shows that the AGKP
acylindrical-hyperbolicity route is not universal.  The former statement that
`SL₃(ℤ)` remained an open selflessness case is now obsolete: Vigdorovich,
arXiv:2602.10616v3, proves that every nontrivial linear group with trivial
amenable radical has selfless reduced C\*-algebra.  Since C\*-simplicity forces
the amenable radical to be trivial, his theorem settles selflessness (and
hence strict comparison) for `SL₃(ℤ)` by a different mechanism.
