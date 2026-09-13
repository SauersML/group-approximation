---
rg: 2
id: elementary-groups-over-polynomial-f-p-rings-are-fp
kind: claim
title: E_n(F_p[s_1..s_k]) equals the Steinberg group St_n and is finitely presented for n >= max(4, k+3)
distinct_from:
  elementary-groups-over-polynomial-s-integers-are-fp: that is Z[1/m][t_1..t_k], where K_2 is nonzero and the proof pulls back kernel generators from SL_n(Z[1/m]); this is F_p[s_1..s_k], where the unstable K_2 kernel vanishes, so the elementary group is the Steinberg group itself.
  steinberg-finite-presentation-and-kazhdan-theorem: that is finite presentation of St_n(R) for finitely presented rings, with no conclusion for E_n(R); this controls the kernel over polynomial rings over F_p.
---

**ESTABLISHED (2026-09-13)** through
`elementary-groups-over-polynomial-f-p-rings-are-fp-proof`. It imports K-theory
from textbooks, as listed in the route. Not independently reviewed. No novelty is
claimed: it is very likely known to experts, and it follows from the same imports
as `elementary-groups-over-polynomial-s-integers-are-fp`.

**Statement.** Let `p` be a prime, `k >= 0`, `R = F_p[s_1, ..., s_k]` and
`n >= max(4, k+3)`. Then `ker(St_n(R) -> E_n(R)) = 0`. So `E_n(R) ≅ St_n(R)`,
and `E_n(R)` is finitely presented.

**Special case.** `E_4(F_p[s])` is isomorphic to `St_4(F_p[s])` and finitely
presented.
