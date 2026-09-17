---
rg: 2
id: finite-field-upper-triangular-cloning-groups-do-not-embed-in-v
kind: claim
title: "For a finite field F_q, the Witzel–Zaremsky group T(B_*(F_q)) does not embed in Thompson's group V"
distinct_from:
  char-zero-upper-triangular-cloning-groups-do-not-embed-in-v: that is the characteristic-0 case, which follows from Corwin's theorem; here the base group is finite and the needed non-embedding of C_p ≀ Z^2 is open
  some-finite-cloning-system-group-does-not-embed-in-v: that is the bit-register system on symmetric groups, settled by period growth; here period growth gives nothing
---

**OPEN.** Route `finite-field-upper-triangular-cloning-not-in-v-via-lamplighter` reduces this claim to
`cyclic-p-wreath-z2-does-not-embed-in-thompson-v`.

**Claim.** For every prime power `q`, the Thompson-like group of the Witzel–Zaremsky upper-triangular
cloning system on `B_n(F_q)` (arXiv:1405.5491, §7) is not isomorphic to a subgroup of `V`.

## Attempts

- 2026-09-17 (swarm-0917-w5-pull-z-1).
  - *Period growth fails.* Torsion of `T(B_*(F_q))` lives in `B_∞(F_q)`. Every element of `B_n(F_q)`
    has order dividing `(q−1)·p^⌈log_p n⌉ ≤ (q−1)pn`, so the orders grow linearly and the method of
    `bit-register-cloning-group-has-doubly-exponential-period-growth` gives no obstruction.
  - *Subgroup obstruction.* The group contains `C_p ≀ Z^2`. Whether that group lies in `V` is open.
