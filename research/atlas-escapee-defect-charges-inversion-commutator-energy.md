---
rg: 2
id: atlas-escapee-defect-charges-inversion-commutator-energy
kind: claim
title: Every improved Atlas cartesian escapee pays gauge-invariant inversion commutator energy
distinct_from:
  atlas-true-criterion-baseline: that computes the tensor-flip defect sqrt(2) on the seventy-two single-factor escapees; this gives a pointwise lower bound on the cross-chart energy required to reduce any one of those defects.
  atlas-full-relator-data-factor-through-double-commutant-gauge: that identifies the intrinsic double-commutant quotient of all word data; this exhibits an explicit nonnegative function on that quotient which every improved escapee must charge.
  atlas-equal-block-flattening-is-commutant-gauge: that proves equal operator-block norms can be installed without moving any word defect; this proves that moving an escapee requires a genuinely gauge-invariant cross-chart change.
---

**ESTABLISHED LOCAL OBSTRUCTION.**  Let `rho_1,rho_2` be regular
amplifications of a finite group `A`, and put

```text
A_g=rho_1(g),                 B_h=U rho_2(h) U^*.
```

For a two-chart word `w`, let `p_1(w),p_2(w)` be its factor products and let
`Inv(w)` be the set of pairs consisting of a second-chart letter occurring
to the left of a first-chart letter.  Write `N_w=|Inv(w)|` and

```text
E_w(U)=sum_((h,g) in Inv(w)) ||[A_g,B_h]||_2^2.       (EIC1)
```

If `(p_1(w),p_2(w))=(a,1)` with `a != 1`, or symmetrically `(1,b)` with
`b != 1`, then, for

```text
delta_w(U)=||pi_U(w)-1||_2,
```

one has

```text
sum_Inv ||[A_g,B_h]||_2 >= sqrt(2)-delta_w(U),        (EIC2)
E_w(U) >= (sqrt(2)-delta_w(U))_+^2/N_w               (EIC3)
```

when `N_w>0`.  If `N_w=0`, the word is already factor-sorted and
`delta_w(U)=sqrt(2)` for every `U`.

The energy `(EIC1)` is invariant under the complete relative gauge

```text
U -> D U C,       D in rho_1(A)', C in rho_2(A)'.    (EIC4)
```

Indeed each cross commutator is merely conjugated by `D`.  Consequently any
operator-valued biunitary, unitary-error-basis, Hadamard, or quantum-Latin
ansatz which decreases one of the seventy-two single-factor escapee defects
from its tensor-flip value `sqrt(2)` to `epsilon` must create the fixed
gauge-invariant cross-chart energy

```text
E_w(U) >= (sqrt(2)-epsilon)^2/N_w.                    (EIC5)
```

At the tensor flip all cross-chart commutators vanish and the escapee defect
is `sqrt(2)`, so the inequality is sharp at the known baseline endpoint.

**SCOPE FIREWALL.**  This is not yet a lower bound for the full Atlas
criterion.  It does not prove that the already-satisfied cartesian control
relators dominate `E_w(U)`.  The exact remaining local endpoint is an
estimate of the form

```text
E_w(U) <= C_w sum_(s in controls) ||pi_U(s)-1||_2^2   (EIC6)
```

for at least one actual escapee `w`, or a countermodel to every such
estimate.  Existing first-order rigidity and the bounded translation-sector
Hessian screen do not supply `(EIC6)`, while the dense small-group examples
already show that active traces are not globally constant.  Thus `(EIC3)`
rules out gauge-only flat-block progress but does not by itself select the
hyperlinear or non-hyperlinear branch.

For the exact three-term decomposition of the shortest escapee and the proof
that its literal four-syllable controls reach only one parabolic term, see
`atlas-shortest-escapee-literal-control-firewall`.  That result fences the
naive pointwise telescope but leaves `(EIC6)` for the full control family
open.

DERIVATION
atlas-escapee-inversion-energy-proof
