---
rg: 2
id: bf-n-r-pulled-back-characters-follow-endpoint-hull-by-degree
kind: route
title: "Split the pulled-back formula into the Sigma^1 statement, the pulled-back holes, and Sigma^m lifting"
target: bf-n-r-pulled-back-characters-follow-endpoint-hull
requires:
  - bf-n-r-pulled-back-sigma-one-misses-only-endpoint-characters
  - bf-n-r-sigma-m-holes-of-f-n-r-pull-back
  - bf-n-r-pulled-back-sigma-m-lifts-off-endpoint-hull
---

- The `m = 1` bullet is `bf-n-r-pulled-back-sigma-one-misses-only-endpoint-characters`.
- For `m >= 2`, "if": the nonnegative hull is a hole by `bf-n-r-sigma-m-holes-of-f-n-r-pull-back`.
- For `m >= 2`, "only if": every character off the hull lies in `Sigma^m` by
  `bf-n-r-pulled-back-sigma-m-lifts-off-endpoint-hull`, the one open prerequisite.
