---
rg: 2
id: atlas-seven-word-a9-a10-exclusion-proof
kind: route
title: Read the six first-failure indices and the unique 19243-killed survivor
target: atlas-seven-word-a9-a10-exclusion
requires: []
artifacts:
  - experiments/atlas-a9-two-chart-scan-v2.json
  - experiments/atlas-a10-two-chart-scan.json
---

Both archived scans are exhaustive and report `timed_out=false` with tested
counts equal to the expected numbers of chart positions.  In both files the
`first_boundary_failure_histogram` has support exactly

```text
{0,2,11,30,44,55}.
```

Therefore surviving those six boundary words is equivalent, inside the
scanned geometry, to surviving the whole ordered `234`-word boundary list.
Each file records exactly one such boundary survivor and
`combined_survivor_count=0` when interior index `19243` is added.  This is
precisely the seven-word statement.
