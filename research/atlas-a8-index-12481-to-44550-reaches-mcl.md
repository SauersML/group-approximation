---
rg: 2
id: atlas-a8-index-12481-to-44550-reaches-mcl
kind: claim
title: The first arithmetic A8-overgroup candidate after G2(4) is McL at index 44550
distinct_from:
  atlas-a8-index-12145-to-12480-reaches-g24: that pins the preceding G2(4) endpoint; this crosses the complete interval from G2(4) to McL.
  atlas-mcl-contains-no-a8: that excludes the endpoint by subgroup structure; this only identifies it by simple-group order.
---

Let `S` be finite nonabelian simple and suppose `|A8|=20160` divides
`|S|`.  If

```text
12480 < |S|/20160 <= 44550,                          (SIMCL-1)
```

then

```text
S ~= McL,                 |S|/20160 = 44550.        (SIMCL-2)
```

Indeed, the complete simple-group order table from `G2(4)` through `McL`
has no intervening row whose displayed prime factorization contains
`2^6*3^2*5*7=20160`.  At the endpoint,

```text
|McL| = 898128000 = 44550*20160.                    (SIMCL-3)
```

Source: the GAP Character Table Library
[*Simple Groups by Group Order*](https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctbllib/ctbltoc/views/simplebyorder.html).

