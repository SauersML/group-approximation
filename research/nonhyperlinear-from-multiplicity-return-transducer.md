---
rg: 2
id: nonhyperlinear-from-multiplicity-return-transducer
kind: route
title: Predicate rank gates plus a returning multiplicity wire forbid microstates
target: non-hyperlinear-group
requires:
  - multiplicity-return-transducer
  - predicate-rank-gate-doubles-restriction-multiplicity
  - non-ce-bcs-has-finite-dimensional-forbidden-mass-gap
  - marked-hs-separation-forces-spectral-density
  - bounded-overlap-syndrome-energy-accounting
---

`multiplicity-return-transducer` supplies the finitely presented `Gamma`, the
marked word `w`, the context packets and the transport network.  Suppose
`Gamma` were hyperlinear.  Then there are trace-preserving finite-dimensional
microstates with relator defect `E(U_n) -> 0` in which `w` remains
`alpha`-separated, since hyperlinearity gives an injective embedding into the
hyperfinite tracial ultrapower and `w != 1` in `Gamma`.

`marked-hs-separation-forces-spectral-density` converts that separation into a
spectral carrier of trace at least `3 alpha^2/(16 - alpha^2)`, which is clause 1
of the transducer's input.

On the packets carried by that fraction of the carrier,
`predicate-rank-gate-doubles-restriction-multiplicity` says a context whose
assignment is forbidden returns the baseline spin packet **twice** rather than
once, by `(PRM1)`.  The forbidden assignments occur with total mass at least
`beta_B` by `non-ce-bcs-has-finite-dimensional-forbidden-mass-gap`, and since
every forbidden simple has dimension `2^(N_c+1)`, clause 3 of the transducer
converts that mass into a multiplicity surplus of at least
`beta_B / 2^(1 + max_c N_c)` per unit dimension -- an `Omega(d)` integer defect.

Clauses 2, 4 and 5 then force at least `c eta d` Hilbert dimension into the
transport defect while the defect is bounded by `C E(U_n) d`; since the packet
size is fixed the two are comparable, and
`bounded-overlap-syndrome-energy-accounting` sums the local charges with bounded
incidence into `E(U_n) >= c eta / C > 0`.  This contradicts `E(U_n) -> 0`.

**Soundness conditions this route depends on, both mandatory.**  First, the
premise must satisfy `multiplicity-surplus-is-blind-to-the-non-ce-input`: the
transducer must visibly consume the non-embeddability of `B`, since every step
of the argument above after the forbidden-mass bound is a function of `beta_B`
alone, and a classically unsatisfiable CSP would supply such a constant while
the compiled group is hyperlinear.  Second, clause 4's fixed packet size is not
cosmetic: without it `(PRM1)` conserves Hilbert dimension and the surplus is
invisible to normalized Hilbert--Schmidt norm.
