---
rg: 2
id: fanizza-native-signal-groupification
kind: claim
title: Groupify the Fanizza family with one HALT witness and a computable finite-matrix decoder modulus
artifacts:
  - research/artifacts/fanizza-native-signal-diagonal-2026-08-20.md
distinct_from:
  relative-rank-one-fanizza-groupification: that asks for universal machine-independent constants and a separate Boone word feeding a positive nonmember carrier; this retains the native signal word, allows computable index-dependent constants, and uses the reverse Kleene diagonal.
  hs-groupify-self-referential-bcs-signal: that first fixes one algebraically self-referential BCS and must preserve algebraic nonzeroness through groupification; this groupifies the computable family before taking the fixed point.
---

For the computable Fanizza `HALT`-family `B_m`, construct computably a finite
group presentation

```text
Gamma_m=<S_m|R_m>
```

which retains every original BCS involution as a named generator, in
particular `d_m=x_(D,m)`, and computable finite constants `A_m,B_m` with the
following properties.

1. If machine `m` halts, there is some exact representation of `Gamma_m`, on
   an arbitrary Hilbert space, in which `d_m` is nonidentity.  It is enough
   that one amplification of the membership GNS model extends.  The extension
   need not be tracial, finite, or available for any other BCS representation.
2. From every finite-dimensional unitary tuple `U` of relator defect
   `eta=Def_(R_m)(U)`, one obtains a commuting-operator strategy `S_U` for
   `B_m`, with exact Bob involution `X_(D,m)`, such that

```text
epsilon(S_U) <= A_m eta^2,                                      (NSG1)
||U(d_m)-X_(D,m)||_2 <= B_m eta.                                (NSG2)
```

The constants need only be computable from the finite index `m`.  They need
not be uniform over the family and must not depend on whether, or after how
many steps, machine `m` eventually halts.  Context selectors must remain
local: the construction is invalid if it globally centralizes them and turns
the BCS into a classical CSP.

## Attempts

- **Separate Boone carrier: unnecessary for this target.**  The exact
  calculation `(NSM3)` already identifies the marked-word distance with the
  native signal mass.
- **Tracial extension on the HALT side: unnecessary.**
  `kleene-completeness-needs-only-a-nontrivial-exact-representation` shows that one
  nontrivial exact representation certifies `d_m!=1`.  Countable amplification
  makes its carrier absorb every fixed finite copy or packet multiplicity
  demanded by a completion gadget.  Only the finite-matrix soundness clauses
  `(NSG1)--(NSG2)` require quantitative trace control.
- **Uniform compiler constants: unnecessary for this diagonal.**  Once the
  recursion theorem fixes `m_*`, any positive computable modulus at that one
  index contradicts canonical-trace microstates.
- **Live finite packet route.**  Use the S3-equivariant radical packets to
  charge every nonlinear forbidden assignment, preserve the original shared
  involutions, reset before installing the next context, and sum the finitely
  many local decoder losses into `A_m,B_m`.  The remaining construction is
  the fresh-context return; no runtime-uniform Boone coupling remains.
- **Shared-implementer reversible circuit.**  The alternative route
  `fanizza-native-signal-via-shared-multiplicity-circuit` uses commutators of
  controlled Pauli gates to compute nonlinear conjunctions.  Its sole new
  gate is to make the external multiplicity implementers commute or coincide
  without identifying the different selector controls.
- **Native involution as local predicate carrier: impossible.**
  `single-involution-cannot-be-a-nonlinear-selector-carrier` evaluates its
  selector corners in the regular trace.  Outside the selector subgroup every
  atom has positive carrier mass; inside it the carrier detects only one
  affine parity half-space.  The word `d_m` remains the final mark, while the
  nonlinear predicate must be carried by a higher-dimensional packet or by
  multiplicity holonomy.
