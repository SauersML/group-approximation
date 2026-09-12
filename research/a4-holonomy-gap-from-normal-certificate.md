---
rg: 2
id: a4-holonomy-gap-from-normal-certificate
kind: route
title: The minimal three-edge conjugacy star around 19243 forces complete chart-frame collapse
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-collision-assisted-opaque-star-compiler
  - unitary-star-conjugacy-hs-collapse
  - atlas-a8-four-cycle-commutant-gap
---

Use the four raw covariance opcodes for

```text
T={t01,t12,t23,t30}
```

defined by `(A4-STAR-0)`, and abbreviate

```text
B_n=V_n(t23),
T_(n,t)=V_n(t),       t in {t01,t12,t30}.
```

The compiler supplies three opaque transport unitaries `A_n(t)` with

```text
max_(t in {t01,t12,t30})
 ||T_(n,t)-A_n(t)B_nA_n(t)^*||_2
 <= C_star (||sigma_n(q_19243)-1||_2+eta_n),            (1)

||B_n-1||_2
 <= C_col (||sigma_n(q_19243)-1||_2+eta_n).             (2)
```

Apply `unitary-star-conjugacy-hs-collapse`:

```text
max_(t in T)||V_n(t)-1||_2
 <= C_star (||sigma_n(q_19243)-1||_2+eta_n)
    + C_col (||sigma_n(q_19243)-1||_2+eta_n)
 -> 0.                                                   (3)
```

By definition `(A4-STAR-0)`, these are exactly the four covariance
commutators.  Apply `atlas-a8-four-cycle-commutant-gap`:

```text
dist_2(U_n,lambda_(k_n)(A8)')
 <= 17 sqrt(4) max_(t in T)||V_n(t)-1||_2
 -> 0.                                                   (4)
```

Choose a nearest commutant element `Y_n`.  For each fixed raw-S3 covariance
generator `h_a,h_b`,

```text
||[U_n,lambda(h)]||_2 <= 2||U_n-Y_n||_2 -> 0.
```

Hence `a_n^2+b_n^2->0`, stronger than `limsup<1/128`, proving
`atlas-a4-holonomy-coherence-gap`.

By `atlas-a8-minimal-four-transvection-cycle`, this transvection-star incidence
pattern is minimal: three leaves are necessary if the hub and leaves are to
form a transvection generating set for the full chart.  The live direct
portfolio therefore asks for the smallest possible finite synchronization
object of this type—three opaque transports plus one collision readout.
