---
rg: 2
id: fixed-section-positive-packet-gaps-escape-bounded-dimension
kind: claim
title: A fixed quotient section makes every bounded-dimensional positive packet gap vanish
distinct_from:
  positive-packet-witness-gap-endpoint: that compactifies a persistent gap across arbitrary moving packet dimensions into a quotient separator; this proves that no persistent sequence can remain in bounded matrix dimension, and that changing from one externally fixed section to another has asymptotically no effect.
  cross-face-choi-annihilation-is-scalar-partition: that gives one hard finite packet after choosing a section for that packet; this treats a section fixed before an exhausting packet sequence and proves exactly what such external fixation buys.
  native-relator-soft-modes-persist-in-simple-ideal-blocks: that constructs irreducible full-ideal packets with low native-relator Rayleigh energy; this concerns the normalized affine Choi gap itself and is uniform over every representation of bounded dimension.
---

**ESTABLISHED (fixed-section dimension escape).**  Let

```text
q:A->>Q=A/I,
E subset Q a finite-dimensional operator system,
t:E->A unital, self-adjoint and linear,       q t=id_E,     (FSG1)
```

and let `L_1 subset L_2 subset ... subset I` be finite-dimensional
self-adjoint spaces with dense union.  Put

```text
V_m={v in L_sa(E,L_m):v(1)=0}.                            (FSG2)
```

Fix `D<infinity`.  Uniformly over all unital finite-dimensional
representations `rho:A->M_d`, `d<=D`,

```text
inf_(v in V_m) dist(rho o (t+v),UCP(E,M_d)) ->0.          (FSG3)
```

No RFD hypothesis is needed.

Now specialize to the Kac--Moody triangle ideal-block problem.  For each `m`
let `rho_m:A->M_(d_m)`, let `J_m=rho_m(I)` have central unit `z_m`, and let
`Omega_m` be any real functional on the self-adjoint map space `E->J_m`
satisfying

```text
||Omega_m||<=C,
Omega_m(z_m rho_m o v)=0       for every v in V_m.        (FSG4)
```

Define its normalized affine advantage against the relative-unital Choi
slice by

```text
gamma_m(t)=Omega_m(z_m rho_m o t)
 -sup_(theta in UCP_(z_m)(E,J_m))Omega_m(theta).           (FSG5)
```

If `sup_m d_m<=D`, then

```text
limsup_m gamma_m(t)<=0.                                  (FSG6)
```

In particular the positive witnesses from
`ideal-block-infeasibility-has-positive-reservoir-witness`, for which
`gamma_m(t)>0` and `C=C_Delta`, necessarily satisfy

```text
gamma_m(t)->0                                             (FSG7)
```

along every bounded-dimensional packet sequence.  Thus a positive tail gap
forces `d_m->infinity` after passage to a subsequence.  This remains true if
every `rho_m` is irreducible and

```text
rho_m(I)=M_(d_m).
```

Simple full ideal blocks do not close the gate; they merely locate its only
surviving escape in unbounded matrix dimension.

The phrase **one externally fixed section** is also asymptotically
section-independent.  If `t':E->A` is another fixed unital self-adjoint
section and the same bounded witnesses satisfy `(FSG4)`, then

```text
|gamma_m(t)-gamma_m(t')|->0,                              (FSG8)
```

with no bound on `d_m`.  Hence replacing one fixed lift by another cannot
create or remove a persistent normalized gap.  What cannot be replaced this
way is a section `t_m` re-chosen after seeing packet `rho_m`: the differences
`t_m-t` need not admit uniformly accurate depth-`m` reservoir
approximations.

**Consequence for the live triangle gate.**  RFD, irreducibility, maximal
ideal support and external fixation of `t` do not prove `gamma_m->0` in the
only regime still relevant.  A completion must control an
**unbounded-dimensional diagonal family** of simple ideal blocks, or prove a
dimension-free estimate coupling the fixed section's affine Choi discrepancy
to the native relators.  Repeating the fixed finite-packet construction from
`cross-face-choi-annihilation-is-scalar-partition` cannot supply such a
family, but compactness of bounded-dimensional representation varieties
cannot rule one out either.

Proof: `compact-bounded-dimensional-packets-and-heal-the-fixed-section`.

DERIVATION
compact-bounded-dimensional-packets-and-heal-the-fixed-section
