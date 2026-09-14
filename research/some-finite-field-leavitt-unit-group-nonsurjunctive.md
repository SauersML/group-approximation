---
rg: 2
id: some-finite-field-leavitt-unit-group-nonsurjunctive
kind: claim
title: Some unit group of a Leavitt algebra over a finite field is not surjunctive
root: true
distinct_from:
  leavitt-unit-group-nonsurjunctive: that is the binary host over F_2 with d = 2; this asks for any host L_(F_q)(1,d)^x, of which a counterexample on the binary host is a special case.
  ternary-leavitt-unit-group-nonsurjunctive: that is the single host over F_3 with d = 2; this allows every prime power q and every arity d.
artifacts:
  - research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md
---

**OPEN.** Exhibit a prime power `q`, an arity `d >= 2`, and an injective, non-surjective cellular
automaton over `L_(F_q)(1,d)^x` with a finite alphabet. It refutes
`gottschalk-surjunctivity-conjecture`.

*Marked `root` because it heads the counterexample search over all finite-field Leavitt hosts at once,
as `leavitt-unit-group-nonsurjunctive` does for one host.*

## Attempts

- **Linear route.** Reduced to `leavitt-visible-cyclic-corner-is-full-on-some-host` by the route
  `cyclic-corner-fullness-refutes-leavitt-host-surjunctivity`. The image equation already holds in
  the Leavitt algebra on every host. The lift is open.
- **Special cases feed it.** The binary root and the ternary root each imply this one
  (`binary-nonsurjunctivity-gives-finite-field-leavitt-host`,
  `ternary-nonsurjunctivity-gives-finite-field-leavitt-host`).
- **Gromov–Weiss decides no host.** Every host is nonsofic
  (`d-ary-leavitt-groups-nonsofic-over-finite-fields`).
