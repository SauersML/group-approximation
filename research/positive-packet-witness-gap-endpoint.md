---
rg: 2
id: positive-packet-witness-gap-endpoint
kind: claim
title: Positive native packet witnesses compactify exactly when their affine gaps do not degenerate
distinct_from:
  ideal-block-infeasibility-has-positive-reservoir-witness: that constructs a uniformly bounded positive Choi witness for one failed packet and one reservoir; this controls an exhausting sequence and identifies the only numerical datum which can survive the moving packet and moving ideal block.
  exhausting-ideal-reservoirs-have-lift-or-quotient-separator: that uses global reservoir-to-ucp distances and arbitrary signed Hahn--Banach functionals; this starts with the positive native ideal-block certificates themselves and proves that a persistent packet gap already descends to the unit-zero quotient map space.
  positive-tree-separator-has-fd-low-ideal-moment-packets: that starts from an already existing quotient separator and approximates its positive state by finite-dimensional packets; this runs in the opposite direction, from packetwise affine infeasibility to a quotient obstruction.
---

**ESTABLISHED (gap-or-degeneration endpoint).**  Let

```text
q:A->>Q=A/I,
E subset Q a finite-dimensional operator system,
t:E->A unital, self-adjoint and linear,       q t=id_E,     (PGC1)
```

and let `L_1 subset L_2 subset ... subset I` be finite-dimensional
self-adjoint spaces with dense union.  For each `m`, let `rho_m` be a
finite-dimensional representation of `A`, let `J_m=rho_m(I)` with unit
`z_m`, and suppose the depth-`m` ideal-block affine slice is infeasible.
Choose the positive witness furnished by
`ideal-block-infeasibility-has-positive-reservoir-witness`, normalized so
that

```text
||Omega_m||<=C,
Omega_m(v)=0 for every
  v in rho_(m*) L_sa(E,L_m) with v(1)=0,                  (PGC2)
gamma_m:=Omega_m(z_m rho_m t)
          -sup_(theta in UCP_(z_m)(E,J_m))Omega_m(theta)>0. (PGC3)
```

Here `C` is independent of `m`, of the packet dimension, and of `J_m`.
Then:

1. If the inclusion `E subset Q` has a ucp lift to `A`, necessarily

   ```text
   gamma_m ->0.                                           (PGC4)
   ```

2. If `limsup_m gamma_m>0`, a tail subnet of the pulled-back witnesses has a
   bounded weak-star limit on the fixed unit-zero map space

   ```text
   X_0={h in L_sa(E,A):h(1)=0}                            (PGC5)
   ```

   which annihilates `L_sa(E,I) intersect X_0` and strictly separates
   `t-s` from zero for every `s in UCP(E,A)`.  It therefore descends to a
   quotient-level separator and proves that `E` has no ucp lift.

Thus positivity and packet-dimension conditioning have reduced the remaining
compactness issue to one scalar question: **do the normalized affine gaps
degenerate?**  No additional compatibility of the Choi matrices, packet
dimensions, or support projections is needed if the gaps stay positive.
Conversely positivity alone cannot stop degeneration.

That last limitation is exact even in dimension two.  Put

```text
E=C^2,       J=M_2,       L=C I_2,
A_0=diag(2,-1),
T(delta_1)=A_0,       T(delta_2)=I_2-A_0,                 (PGC6)
```

and let the unit-zero correction space consist of

```text
v_c(delta_1)=c I_2,   v_c(delta_2)=-c I_2   (c real).     (PGC7)
```

No `T+v_c` is ucp.  Nevertheless the functional

```text
Omega(phi)=<phi(delta_1)f_1,f_1>
           +<phi(delta_2)f_2,f_2>                         (PGC8)
```

is positive on every cp map, annihilates every `v_c`, has

```text
Omega(T)=4,       sup_(theta in UCP(E,M_2))Omega(theta)=2, (PGC9)
```

while the sole reservoir generator has no soft vector at all:

```text
||I_2 xi||^2=1       for every unit vector xi.             (PGC10)
```

Hence an individual positive affine Choi witness cannot, by order theory
alone, be converted into a low-reservoir-energy vector.  Any such conversion
in the Kac--Moody triangle must use additional relations tying the specific
native relator reservoir to the Choi defect; `(PGC8)--(PGC10)` rules out an
abstract positivity-only argument.

Proof: `positive-packet-gap-compactness-proof`.

DERIVATION
positive-packet-gap-compactness-proof
