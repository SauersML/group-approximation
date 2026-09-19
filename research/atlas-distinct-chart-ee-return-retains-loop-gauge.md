---
rg: 2
id: atlas-distinct-chart-ee-return-retains-loop-gauge
kind: claim
title: The first distinct-chart return of x12(ee) retains the seam loop gauge
invalidates:
  - atlas-distinct-chart-ee-return-authenticates-common-mode
artifacts:
  - experiments/atlas_first_nonscalar_mixed_row_audit.py
distinct_from:
  atlas-two-e-strip-return-retains-common-gauge: that returns x12(ee) to the chart-one root p1_23 and leaves one nested nuisance; this applies the shortest root-position Weyl transport to a literal generator in the other atlas chart.
  three-chart-loop-retains-free-multiplicity-holonomy: that treats abstract full-chart transports and inserts a spectator on a general three-cycle; this audits one explicit two-chart Atlas consequence and computes its nuisance-quotient rank.
  monomial-root-elements-are-conjugate-in-the-leavitt-group: that gives abstract conjugacy of every monomial root to a unit root; this identifies an explicit packet word landing on p2_23 and shows why the transported occurrence still is not a scalar reservoir authentication.
---

**ESTABLISHED DISTINCT-CHART QUOTIENT-RANK FENCE.** Let `N_1` be the
two-`E` nested return from `atlas-two-e-strip-return-retains-common-gauge`:

```text
N_1=[x_13(E),[x_31(E),x_12(ee)]]=x_12(1)=p1_23.       (DCR1)
```

In characteristic two put

```text
w_ij=x_ij(1)x_ji(1)x_ij(1),       H=w_13 w_24.        (DCR2)
```

The two disjoint Weyl swaps send the ordered root `(1,2)` to `(3,4)`.
Consequently

```text
N_2=H N_1 H^(-1)=x_34(1)=p2_23.                       (DCR3)
```

This is the first root-position continuation of `(DCR1)` which lands on a
literal generator of the other atlas chart: changing both entries of the
ordered pair requires two root transpositions. The MSI audit expands the
fixed word, verifies `(DCR3)` by exact binary Leavitt arithmetic, and finds

```text
length(H)=20 syllables,
length(N_2 p2_23^(-1))=160 syllables,
Atlas-X-length(N_2 p2_23^(-1))=479.                    (DCR4)
```

Despite the second authenticated chart endpoint, no third scalar quotient
direction appears. Take desired columns `(P_3,P_4,P_5)` from the common-RHS
star and mandatory nuisance columns `(R,N_1,N_2)`. After the two chart
outputs are exactified, the five homogeneous rows have matrices

```text
C=[ I_3 ; 0 ; 0 ],
D=[ -1_3  0  0 ; 0  1  0 ; 0  0  1 ].                 (DCR5)
```

Hence

```text
rank[C D]=5,              rank(D)=3,
rank[C D]-rank(D)=2.                                  (DCR6)
```

The exact projected gauge from the first return survives unchanged. For an
arbitrary nonidentity invertible `U`, set

```text
P_3=P_4=P_5=R=U,
x_31(E)|_mult=U^(-1),       x_13(E)|_mult=I.           (DCR7)
```

Then `N_1=I`. Give the Weyl transporter any multiplicity spectator `W`.
Since `Ad_W(I)=I`, also `N_2=I`; both chart endpoints and all five projected
rows are exact while `U` and `W` remain arbitrary. Over `GL_d(F_2)` these
coefficient products are realized by elementary block transvections.

Thus even a literal occurrence on the second chart is only a transported
nested nuisance unless the transporter itself is authenticated relative to
the return-star reservoir. This is a countermodel to the scalar
nuisance-rank route for this selected family, not a model of all 4,648
packet words. The next useful row must compare one chart endpoint directly
with the unstripped common mode, or close the relative Weyl/nested loop on a
payload occurrence rather than merely conjugate its identity output.

DERIVATION
atlas-distinct-chart-ee-return-loop-proof
