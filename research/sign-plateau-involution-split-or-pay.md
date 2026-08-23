---
rg: 2
id: sign-plateau-involution-split-or-pay
kind: claim
title: A sign plateau is paid by the involution row or becomes an almost reducing summand
distinct_from:
  opposite-root-orthogonality-charges-two-jump-gauges: that handles arbitrary root-algebra unitary gauges in a regular packet through trace orthogonality; this is representation-independent but treats sign gauges attached to projections.
  two-jump-cycle-refutes-functional-calculus-gauge-bound: that shows two small shift boundaries can separate large plateaux; this proves the full involution row detects exactly whether those plateaux reduce the Weyl involution.
  regular-iwahori-relative-congruence-exactification: that must globally round the resulting almost reducing payload; this supplies only the first exact split-or-pay step.
---

Let `x` be an involution, let `P` be a projection, and put

```text
c=1-2P,       x'=c x.
```

Then the involution-row defect is exactly

```text
||(x')^2-1||_2=2||[P,x]||_2.                           (SPI1)
```

Moreover there is a projection `Q` commuting with `x` such that

```text
||P-Q||_2<=||[P,x]||_2.                                (SPI2)
```

Consequently, for any other unitary `g`,

```text
||[Q,g]||_2<=||[P,g]||_2+2||[P,x]||_2.                (SPI3)
```

Apply this to a phase plateau projection in the exact BS commutant.  Such a
`P` commutes with the root `s`; its commutator with the shift `r` is exactly
its cycle-boundary energy.  Hence either the full involution row pays the
plateau through `(SPI1)`, or `(SPI2)--(SPI3)` replace it by an `x`-reducing
projection which still almost reduces `s` and `r`.  This is the rigorous
first stage of the proposed plateau mechanism:

```text
nonreducing plateau -> fixed relator energy,
nearly reducing plateau -> approximately common summand.             (SPI4)
```

What remains is not phase functional calculus.  It is a global rounding
theorem for the approximately common summand `Q` in arbitrary
noncongruence modular-vertex payloads.  On congruence packets the completed
mixed repair theorem performs that rounding; regular tensor camouflage
shows canonical fixed traces alone do not perform it.

