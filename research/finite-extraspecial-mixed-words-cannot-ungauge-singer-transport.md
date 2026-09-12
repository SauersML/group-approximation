---
rg: 2
id: finite-extraspecial-mixed-words-cannot-ungauge-singer-transport
kind: claim
title: Finite extraspecial mixed words cannot cancel the gauge while moving Singer support
invalidates:
  - finite-extra-double-gauge-moving-bridges
artifacts:
  - research/finite-extraspecial-singer-gauge-proof.md
distinct_from:
  fano-semidir-bridges-are-wrong-subgroup-or-gauged: that separates pure coefficient and actor-moving elements in the original finite Fano semidirect packet; this permits arbitrary finite normal extraspecial enlargements and any number of outer gauge-bearing occurrences.
  label-only-dressing-cannot-ungauge-a-whitehead-bridge: that treats a composite containing exactly one gauged Whitehead and otherwise label-only factors; this treats multiple gauged mixed normalizer letters and identifies their total projective quotient gauge.
  el20-six-moving-coefficient-square-bridges: that still permits a nonnormal opposite-root/full-Leavitt occurrence leaving every finite normal extraspecial packet; this rules out the entire finite normal-extension version of the remaining search.
---

**ESTABLISHED FINITE-EXTENSION FENCE.**  Let `E normal H` be a finite
extraspecial `2`-group with central involution `J`, and let `L=H/E`.  On the
`J=-1` sector, Clifford theory writes every representation of `H` as

```text
pi|_E=rho tensor I_M,
pi(w)=U_(ell) tensor V_(ell),          ell=wE in L.     (FEM1)
```

Here `rho` is the unique spin representation of `E`, `U_ell` is a fixed
spin implementer, and `V_ell` runs through the projective modules of the
appropriate twisted group algebra of `L`.

Suppose the finite packet contains the signed Hecke source over `L_0` and
its first Singer translate over `tL_0t^(-1)`, with

```text
tL_0t^(-1) != L_0.                                    (FEM2)
```

Any word `w` which has exact full source and range Grams from the first cut
to the second has nontrivial quotient `ell=wE`.  Indeed, conjugation by an
element of `E` preserves the actor-quotient support `L_0`, while the target
support is the different subgroup in `(FEM2)`.

For `ell!=1`, the factor `V_ell` in `(FEM1)` cannot be the identity, or even
one fixed scalar absorbable into `U_ell`, in every marked representation.
The twisted regular representation is faithful on the basis element
`u_ell`, so some marked projective quotient module sees a non-scalar or
different action.  Consequently the packet relations do not imply a typing

```text
pi(w)=U_(ell) tensor I_M.                              (FEM3)
```

This remains true when `w` is a product of two, four, or arbitrarily many
gauge-bearing Whitehead, Clifford, or mixed coefficient normalizer letters.
Their individual reservoir factors multiply projectively to the single
quotient factor `V_(wE)`; they cancel universally only when the total
quotient is trivial.  But a trivial quotient cannot move the Hecke subgroup
support by `(FEM2)`.

Hence adding a second gauged occurrence inside any finite normal
extraspecial enlargement does not repair the known Whitehead bridge.  There
is an exact marked finite-dimensional representation with zero packet
defect and positive distance from `(FEM3)`.  The remaining EL20 candidate
must therefore use a genuinely **nonnormal** opposite-root/full-coefficient
occurrence: one which leaves the selected extraspecial atom algebra rather
than merely enlarging its finite normalizer.

No Property `(T)`, trace-profile hypothesis, approximation theorem, or
Steinberg-kernel lift is used.

## Attempts

- **Cancel by parity of outer occurrences.**  Two copies of a gauge-bearing
  letter do not contribute `D^2` unless their total quotient word is
  trivial.  In the spin decomposition their reservoir factors multiply to
  `V_(wE)`, and support movement forces `wE!=1`.
- **Absorb the remaining quotient action into the label implementer.**  A
  fixed scalar absorption would make the twisted basis element `u_(wE)`
  scalar in the faithful twisted regular representation.  This again forces
  `wE=1` and loses the Singer support movement.

DERIVATION
finite-extraspecial-singer-gauge-proof
