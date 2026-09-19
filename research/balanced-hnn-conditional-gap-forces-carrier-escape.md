---
rg: 2
id: balanced-hnn-conditional-gap-forces-carrier-escape
kind: claim
title: A globally balanced HNN edge converts conditional character imbalance into carrier escape
distinct_from:
  subgroup-hecke-hnn-is-a-regular-safe-rank-actuator: That pays a global reverse fixed-space gap by HNN relator energy; this uses equal global character capacity and converts a gap only after compression by an analytic reached carrier into physical escape.
  primitive-clifford-balanced-atoms-have-hnn-obstruction: That constructs the equal-trace controlled-Clifford source and target atoms and shows the odd Whitehead word cannot be their transporter; this gives the carrier-overlap inequality for any valid balanced transporter.
  compressed-antiphase-menu-implies-btb-escape: That obtains escape from a large menu and cross-Gram capacity; this needs only one balanced edge once a conditional source-target gap is supplied.
---

**ESTABLISHED CONDITIONAL ACTUATOR.**  Let `p_s,p_t` be projections in a
finite tracial algebra, let `U` be unitary, and suppose

```text
U p_s U^*=p_t.                                         (BHC1)
```

Let `Q` be any projection commuting with `p_s` and `p_t`, put

```text
A=Qp_s,                  D=U A U^*.                    (BHC2)
```

Then `D<=p_t`, and therefore

```text
tau(QD)<=tau(Qp_t),
tau(D)-tau(QD)>=tau(Qp_s)-tau(Qp_t).                  (BHC3)
```

Indeed `p_tDp_t=D`; since `Q` commutes with `p_t`,
`tau(QD)=tau(Qp_tDp_t)<=tau(Qp_t)`.  Thus a conditional gap

```text
tau(Qp_s)-tau(Qp_t)>=eta tau(A)-delta                (BHC4)
```

implies the CBR3 escape estimate with the same `eta` and error `delta`.

The estimate is robust in normalized Hilbert--Schmidt norm.  If fixed finite
packet correction makes `Q,p_s,p_t` exact and the HNN covariance energy gives

```text
||(1-p_t)U p_s||_2^2<=epsilon,                         (BHC5)
```

then

```text
tau(QD)
 <=(sqrt(tau(Qp_t))+sqrt(epsilon))^2
 <=tau(Qp_t)+2sqrt(epsilon)+epsilon.                  (BHC6)
```

For a fixed presentation `epsilon=O(E_pres)`, so `(BHC6)` loses only
`O(sqrt(E_pres))`, independently of matrix dimension.

This actuator is regular-safe even when the global source and target
characters have equal canonical trace.  In particular the controlled-
Clifford atoms

```text
p_s=e z_+,                  p_t=f(z_++z_-)             (BHC7)
```

both have canonical trace `1/8` and admit a character-preserving HNN edge.
No literal unequal-corner conjugacy is asserted.

What remains is the conditional imbalance `(BHC4)` on the **actual reached
carrier**.  For `(BHC7)`,

```text
tau(Qp_s)-tau(Qp_t)
 = (1/4)(tau(Qz_+)-tau(Qz_-))                          (BHC8)
```

when the Pauli ranks are normalized inside each orientation type.  The
canonical balanced packet has equal `z_+` and `z_-` multiplicity, so the
single edge gives zero there.  Finite packet functoriality and the regular
stationary profile prevent manufacturing a uniformly positive version of
`(BHC8)` by adding only more balanced character edges.  A successful use
must couple the orientation imbalance to the forbidden Reynolds payload or
use a finite menu whose conditional gaps cover the reached multiplicity
profile without a stationary cancellation.

Thus `(BHC3)` is a genuine dimension-uniform support-leakage consequence and
a one-edge alternative to CAM4.  It removes the literal-reflection and
residual-`V` problem once a payload-conditioned conditional character gap is
available; it does not itself create that gap.

DERIVATION
balanced-hnn-conditional-carrier-escape-proof

