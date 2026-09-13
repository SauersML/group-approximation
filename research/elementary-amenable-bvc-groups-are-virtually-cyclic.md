---
rg: 2
id: elementary-amenable-bvc-groups-are-virtually-cyclic
kind: claim
title: Every elementary amenable group with property BVC is virtually cyclic
distinct_from:
  elementary-amenable-finite-hirsch-length-bvc-groups-are-vc: that is the established finite Hirsch length case; this is the full elementary amenable class, where the case of infinite Hirsch length is open
---

Every elementary amenable group with property BVC is virtually cyclic, with no finiteness
assumption. von Puttkamer–Wu, arXiv:1607.03790, Remark (b): "We do not know whether Conjecture B
holds for all elementary amenable groups. Groves and Wilson showed that solvable groups satisfy
it." Barnea–Camina–Ershov–Lewis (2025) list only virtually solvable groups among the elementary
amenable cases.

Route `ea-bvc-vc-via-finite-hirsch-length` reduces it to
`bvc-elementary-amenable-groups-have-finite-hirsch-length`, using the established
`elementary-amenable-finite-hirsch-length-bvc-groups-are-vc`.

## Attempts

- Finite Hirsch length: settled (lane z1-07-vc-proof, unreviewed).
- Infinite Hirsch length: see the open prerequisite. Calibration: `Z ≀ Z` lacks BVC.
  1607.03790, Lemma 1.13(c), bounds the number of non-torsion factors in normal series, and
  the base `Z[t^{±1}]` has arbitrarily long chains `(t-1)^k Z[t^{±1}]`.
