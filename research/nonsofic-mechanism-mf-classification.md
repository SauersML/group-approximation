---
rg: 2
id: nonsofic-mechanism-mf-classification
kind: claim
title: MF classification of the existing one-sided-compression nonsofic groups
root: true
artifacts:
  - non_mf_groups_exist.tex
  - notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md
---

**Resolved 2026-08-23.** For the three one-sided-compression lamp mechanisms
currently represented in this graph:

```text
free lamps       -> weak MF (and nonsofic),
commuting C_2    -> not weak MF (and nonsofic),
Clifford lamps   -> not weak MF (and nonsofic).
```

The shared infranormal Kazhdan/compression geometry therefore does not determine
the operator-norm answer. The free-lamp case survives by the amalgam/Fell
absorption construction, the commuting torsion case is killed directly by
pointwise compression-torsion collapse, and the Clifford case is killed by the
central-sign corner obstruction. See `nonsofic-mf-classification-by-lamp-type`.
