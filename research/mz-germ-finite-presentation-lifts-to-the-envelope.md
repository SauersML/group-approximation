---
rg: 2
id: mz-germ-finite-presentation-lifts-to-the-envelope
kind: claim
title: If the near shift group is finitely presented with finitely generated near-index kernel then the Mallery-Zaremsky envelope is finitely presented
distinct_from:
  mz-envelope-fp-forces-two-sided-fg-near-index-kernel: that is the proved converse direction, from the envelope to the germs; this is the open lifting direction, from germs back to the envelope containing FSym(N).
  fp-alt-fin-envelopes-are-unique-solutions-of-their-relators: that characterizes finitely presented envelopes over Alt_fin by uniqueness of relator solutions; this asks for a sufficient criterion stated only through the germ group of E_nu(P).
---

Let `P` be infinite and finitely generated, and `nu : P -> N` a bijection. If `R_nu` is finitely presented and
`ker eta` is finitely generated, then `E_nu(P)` is finitely presented.

By `mz-envelope-fp-forces-two-sided-fg-near-index-kernel` the hypothesis says exactly that
`Q = E_nu(P)/FSym(N)` is finitely presented. So this claim is the lifting gate (G3): the relations of `FSym(N)`,
and the action on it, must follow from finitely many relations once the germ group is finitely presented.

**Why it is not formal.**

- `E_2` contains the Houghton group `H_2 = FSym(Z) ⋊ Z` with index 2: the `E_2`-shift `(s,s^-1)` is a translation
  of `N` in zigzag coordinates. The germ quotient of `H_2` is `Z`, which is finitely presented, while `H_2` is not
  (K. S. Brown's computation of the finiteness length of Houghton groups; recalled, not re-read here).
- `H_2` is not of the form `E_nu(P)`, so it does not refute this claim. It shows only that a proof must use the
  input action `rho(P)`.
- The positive calibration is `zigzag-cyclic-shift-envelope-is-finitely-presented`.

**How this can fail.** A single pair `(P, nu)` with `R_nu` finitely presented, `ker eta` finitely generated and
`E_nu(P)` not finitely presented refutes this claim. That kills the route
`infinite-shift-compiler-via-two-sided-germ-gate`, but not `infinite-shift-higman-compiler`.

## Attempts

- **Houghton-style relator propagation.** Present `FSym(N)` by Coxeter relations near one end, and propagate them
  by conjugation with the lifts of finitely many germ relators. This works in `H_n` for `n >= 3`, where there is room
  to commute disjoint moves. It dies at the step where two lifts of the same germ relator differ by an element of
  `FSym(N)` whose support is not controlled uniformly in `x`. The `E_2`-part alone reproduces `H_2` and has no room.
  Deferred: a proof must exhibit an input-dependent "three independent directions" condition coming from
  `rho(P)` with `P` infinite. No such condition is formulated here.
- **Three directions by passing to H_n (bh-map, 2026-09-18).** The "three independent directions" asked for above
  can be supplied without any input-dependent condition: replace `E_nu(P)` by the Mallery–Zaremsky Houghton-like
  group `H_n(E_nu(P))`, `n >= 3`, which contains it and is again strongly shift-similar
  (`houghton-like-groups-are-strongly-shift-similar`). For `n >= 2` its germ group is finitely presented iff `R_nu`
  is (`houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group`), so the two-sided window is no longer
  needed, and generic enumerations pass. The lifting problem moves to
  `houghton-like-envelopes-lift-finite-presentation-from-germs` (OPEN), where each ray carries the action of `G`
  instead of translations. This claim itself is unchanged.
