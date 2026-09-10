---
rg: 2
id: fpbs-optimistic-search-linear-wall-cost-proof
kind: route
title: Characterize optimistic wall geodesics and count the cached vertical and crossing queries
target: fpbs-optimistic-search-linear-wall-cost
requires:
  - fpbs-optimistic-search-certified-growth
  - fpbs-closed-wall-forces-exponential-search
artifacts:
  - research/artifacts/fpbs/optimistic-search.md
---

Section 3 shows every candidate crosses at an available height of
smallest absolute value, with no extra tree motion. The failed paths
query only the source-side vertical line and closed crossings; the
successful path adds one open crossing and the target-side descent.
Caching leaves exactly (2m+1)+(2m+1)+1+(m+1)=5m+4 queries.
