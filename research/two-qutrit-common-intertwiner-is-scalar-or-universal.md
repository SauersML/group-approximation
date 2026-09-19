---
rg: 2
id: two-qutrit-common-intertwiner-is-scalar-or-universal
kind: claim
title: A common intertwiner at the two-qutrit active atom is packet-scalar or universally charging
artifacts:
  - research/two-qutrit-common-intertwiner-firewall-proof.md
distinct_from:
  two-qutrit-and-atom-has-no-internal-joint-frame: that proves minimality and external-factor separation at the active atom; this adds the sharp normalized-HS charge for any genuinely adjoined common partial intertwiner.
  two-qutrit-and-cell-retains-sectorwise-pauli-gauge: that constructs the exact active Pauli escape on the rank-one conjunction atom; this classifies nontransport common-arrow candidates based at that atom.
  zpc-active-identity-copy-mixed-occurrence-on-a-positive-corner: that asks for a positive model-dependent mixed occurrence; this proves the finite two-qutrit packet itself cannot name one and records the exact common-arrow endpoint such an extraction would need.
---

**ESTABLISHED COMMON-ARROW FIREWALL.**  In the two-qutrit cell put

```text
p=ST=p_(0,0).
```

On the marked spin block `q C[E]q=M_9(C)`, this is the rank-one
projection onto the joint eigenvector `|0,0>` of `Z_1,Z_2`. For the
normal-form packet element

```text
g=J^c X_1^u Z_1^v X_2^s Z_2^t
```

one has

```text
p g p = 0             if (u,s)!=(0,0),
p g p = omega^c p     if (u,s)=(0,0).                  (TCI1)
```

Consequently

```text
p C[E]p=Cp.                                             (TCI2)
```

On an isotypic carrier `C^9 tensor M`, every packet-internal based arrow is
therefore `lambda p tensor I_M`. In particular, every packet-defined
projection below `p tensor I_M` is either zero or `p tensor I_M`. A
proper positive subcorner of the active atom can only come from the
multiplicity coordinates; it is not named by the two-qutrit packet. Moving
to a different rank-one packet atom is selector transport, which is excluded
in the nontransport seam.

There is nevertheless a sharp exact endpoint for any genuinely extracted
common arrow. Let `r<=p tensor I_M` and let `w` be a partial isometry
with

```text
w^*w=r,                    ww^*=s.                      (TCI3)
```

Assume `r` reduces active unitaries `A,B`, `s` reduces identity-label
unitaries `A^o,B^o`, and use normalized Hilbert--Schmidt norm. Set

```text
delta_A=||A^o w-wA||_2,
delta_B=||B^o w-wB||_2,
delta_0=||([A^o,B^o]-1)s||_2.
```

Then the dimension-free common-intertwiner estimate is

```text
||w([A,B]-1)||_2 <=2 delta_A+2 delta_B+delta_0.          (TCI4)
```

For the exact active Pauli gauge `[A,B]r=-r`, this becomes

```text
2 sqrt(tau(r)) <=2 delta_A+2 delta_B+delta_0.            (TCI5)
```

Thus a positive common occurrence would charge the sectorwise Clifford
escape with the desired fixed normalized-HS constant. In the exact case,
commuting identity-label copies and exact common intertwining force `r=0`.

The scope is also the obstruction. Equation `(TCI4)` is purely algebraic
and holds in every tracial C-star algebra, not only in matrices. Therefore
one cannot impose `(TCI3)` and the two exact intertwining rows as a
universal positive common-arrow relation while retaining a tracial model
with positive Pauli escape on `r`. The live ZPC seam is precisely a
finite-matrix extraction theorem: ordinary presentation defects must
produce a model-dependent multiplicity projection `r` and common polar
arrow `w` with a positive-source estimate in finite matrices, while the
infinite escape is not required to contain such a positive common
intertwiner. The rank-one two-qutrit packet supplies the AND atom but no
internal occurrence from which that extraction follows.
