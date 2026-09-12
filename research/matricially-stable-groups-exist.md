---
rg: 2
id: matricially-stable-groups-exist
kind: claim
title: Point-norm matricial stability holds of concrete groups
distinct_from:
  matricial-stability-identifies-radicals: That claim computes `Rad_MF` for every matricially stable group; this one exhibits groups that are matricially stable, so that the other applies to something rather than to an empty class.
artifacts:
  - GroupApproximation/Sofic/MatricialStabilityInstances.lean
  - non_mf_groups_exist.tex
---

Free groups on any index type, and the integers, are point-norm matricially
stable: every operator-norm almost representation is tracked, at every element
and to every tolerance, by a genuine representation.

**Why this needed saying.**  `IsPointNormMatriciallyStable` is defined in this
development and, until 2026-08-16, no theorem in it ever concluded the
predicate.  Clauses 2 and 3 of the manuscript's `prop:stabradical` therefore
quantified over an empty class: true as printed, since the hypothesis is
displayed, but never applicable to any group the corpus knows.  A hypothesis
inhabited by nothing makes its theorem decoration.

**Consequences, all machine-checked.**  With the predicate inhabited, the
identification of `matricial-stability-identifies-radicals` computes the MF
radical of these groups exactly rather than bounding it:

```text
Rad_MF(F_alpha) = Rad_fd(F_alpha) = 1,      Rad_MF(Z) = Rad_fd(Z) = 1 .
```

The conditionality register at `notes/NON_MF_UNCONDITIONAL_BASELINE.txt` loses
its two `open-predicate` rows as a direct result, and the register's
stale-entry rule is what forces their removal: an exemption cannot outlive the
problem it records.
