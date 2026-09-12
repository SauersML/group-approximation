---
rg: 2
id: sl3z-regular-microstates-are-congruence-correctable
kind: claim
title: Regular-trace microstates of the lattice can be replaced by genuine odd-congruence representations
refuted_by:
  - even-congruence-regular-microstates-obstruct-odd-correction
distinct_from:
  sl3-z-weakly-ucp-stable: that asks for unrestricted flexible correction; the present odd-level strengthening is false even for exact regular representations.
  odd-congruence-lambda-exact-sector-collapses: that remains a valid conditional sector theorem; this refutation says arbitrary regular microstates cannot be moved into that sector.
---

**REFUTED.** The odd-congruence target condition is incompatible with exact
regular representations at even congruence levels. Let

```text
Q_m = SL_3(Z/2^m Z),   d_m = |Q_m|,
sigma_m = lambda_(Q_m) o q_m : SL_3(Z) -> U(d_m).
```

The maps `sigma_m` are genuine representations. Because
`intersection_m ker(q_m)={e}`, their normalized characters converge
pointwise to the regular character. Nevertheless they cannot be flexibly
close, even projectively, to representations factoring through odd
congruence quotients. The proof is
[[even-congruence-regular-microstates-obstruct-odd-correction]].

This does **not** refute unrestricted regular-sector flexible HS correction:
`sigma_m` is already exact. It refutes only the proposed requirement that
every correction land at odd level. Consequently
[[odd-congruence-lambda-exact-sector-collapses]] does not by itself provide
a route from arbitrary regular microstates to `(RC3)`.
