---
rg: 2
id: zero-atom-exit-is-the-missing-return-cell
kind: claim
title: All current finite cells admit a bad zero-atom exit; one gated clock commutator is the missing return
distinct_from:
  pauli-zero-atom-removes-acceptance-source-deficit: that proves the zero-control source has the correct fixed mass and isolates PAZ12; this constructs an exact finite countermodel to deriving PAZ12 from the current surrounding cells.
  acceptance-return-is-one-corner-word: that identifies the full fixed-vector row `(W_game-I)P_0Q`; this proves that the strictly weaker zero-atom invariance row already suffices by unitarity and the game contraction.
  mixed-pauli-commutator-authenticates-one-capacity-cut: that authenticates a commutator with the spectral cut of one involution; this shows that all such capacity and reservoir commutators may vanish while the verifier exits the control atom.
---

The Pauli source identity `(PAZ7)` does not combine with the currently named
finite packet, triangle, block-encoding, or mixed-commutator relations to
give `(PAZ12)`.  There is an exact finite packet model in which all those
relations hold and

```text
eta_0(Q)=2^(-m)tau(Q)>0.                                (ZER1)
```

The missing datum is a mixed relation between the **acceptance word**, the
zero-control atom, and the actual capacity source.

## Exact bad-atom model

Use the native classically flat separator assignment

```text
O_P=O_Q=+1                                             (ZER2)
```

and choose `O_D` to be the wrong value for the `C_D` conjunction.  The three
other native contexts admit allowed extensions with the prescribed shared
separator values by
`fanizza-native-additive-incidence-is-one-triangle`.  Thus all shared logical
names, half-edge product ties, and triangle separator equations are exact,
while the `C_D` predicate rejects one private atom.

At the finite packet level, realize that forbidden diagonal character inside
a finite induced packet representation; its existence is the finite-selector
induction barrier.  Let `q_bad` be its nonzero joint atom.  If desired, take a
direct sum with every selected support-menu type on an orthogonal summand.
The selected Schur and Pauli types are then present exactly, but no current
relation puts the capacity source in their summand.  Set

```text
Q=I_ctl tensor q_bad tensor I_edge.                    (ZER3)
```

Put the `m` verifier controls and all incidence-private gauge pairs in one
extraspecial spin packet `E_(m+M)`.  The first `m` Pauli pairs are the fresh
block controls; the remaining `M` pairs are the half-edge factors from
`private-gauges-close-fanizza-triangle`.  Hence the selected spin type,
cross-edge commutators, common central sign, and the half-edge tensor
factorization are all exact.

Use the explicit triangle resets `(IPG12)`, so

```text
U_ZR U_DZ=U_DR.                                        (ZER4)
```

All extra actions are on incidence-private factors and the full triangle
two-cell is exact.

Order the fixed verifier tests so that the rejecting `C_D` predicate is
first.  On `q_bad`, its rejection projection satisfies

```text
L_1 q_bad=q_bad,
Q_1 q_bad=(I-L_1)q_bad=0.                              (ZER5)
```

The controlled reflections `B_j` and their product `W_game` are the exact
finite wreath/Clifford block encoding.  Choose the intended controller
orientation `u_j=I` in `(COR6)`, so every Hecke orientation equation
`(COR15)` also holds exactly.  Since

```text
T_game=Q_m...Q_1,
```

equation `(ZER5)` gives

```text
T_game Q=0,
P_0W_gameP_0Q=0.                                      (ZER6)
```

Therefore, with `G=P_0Q`,

```text
eta_0(Q)
 =||G||_2^2-Re tau(G^*W_gameG)
 =||G||_2^2
 =2^(-m)tau(Q)>0.                                     (ZER7)
```

Every currently proposed mixed **commutator** lock can simultaneously have
zero defect.  Choose all relative multiplicity gauges to be the identity.
For a capacity authentication cell, write `Q=(I+X_Q)/2`, choose its comparison
involution to commute with `X_Q`, and take the authenticated root coordinate
to be the identity.  The bad atom may be chosen as a joint atom for all
finite truth/consistency reflections, so even `W_game` preserves `Q`; taking
the comparison word from the verifier does not change this conclusion.  The
mixed Pauli identity then holds exactly.  These
cells see whether a capacity or multiplicity coordinate was placed on an
independent reservoir; they do not see that `W_game` sends `P_0Q` out of the
zero-control atom.

Likewise, finite root/Plancherel tables may be tensored in exactly and their
designated root coordinates made trivial.  The model is a countermodel to
the listed finite packet/cell implications, not a claim that the still-open
full coefficient-ring kernel-reflection theorem has been disproved.

## A weaker return than fixed-vector equality is sufficient

The full corner word in `acceptance-return-is-one-corner-word` is

```text
(W_game-I)P_0Q.                                        (ZER8)
```

It asks that `W_game` fix the Gram vector.  Finite-matrix soundness needs
less: it is enough to require that `W_game` not **leave the zero-control
atom** on that source.

Indeed put `G=P_0Q`.  The block identity and the finite game contraction give

```text
||P_0W_gameG||_2
 =||T_gameG||_2
 <=rho||G||_2,                rho<1.                  (ZER9)
```

Since `W_game` is unitary,

```text
||(I-P_0)W_gameG||_2^2
 =||G||_2^2-||P_0W_gameG||_2^2
 >=(1-rho^2)||G||_2^2.                                (ZER10)
```

Consequently the corner invariance estimate

```text
||(I-P_0)W_gameP_0Q||_2^2
 <=K E_rel+o(1)                                       (ZER11)
```

already pays the complete source mass.  No phase or fixed-vector comparison
inside `P_0` is required.

## Existing Pauli controls give a finite mixed row

Let `Z_1,...,Z_m` be the computational control involutions.  Since
`Z_jG=G`,

```text
(Z_jW_game-W_gameZ_j)G=(Z_j-I)W_gameG.                (ZER12)
```

Decompose the output by computational bit strings.  On a string of Hamming
weight `k`, the sum of the squared expressions in `(ZER12)` contributes
`4k`.  Therefore exactly

```text
1/4 sum_(j=1)^m ||(Z_jW_game-W_gameZ_j)P_0Q||_2^2
 >=||(I-P_0)W_gameP_0Q||_2^2.                         (ZER13)
```

Combining `(ZER10)--(ZER13)` gives

```text
sum_j||(Z_jW_game-W_gameZ_j)P_0Q||_2^2
 >=4(1-rho^2)2^(-m)tau(Q).                            (ZER14)
```

Thus `m` capacity-gated mixed commutator rows close PAZ12 without asking for
the stronger return `(ZER8)`.  The number `m` is fixed by the static game.

## One finite clock compresses the row to one corner word

The `m` rows can be replaced by one.  In the finite monomial control packet,
choose a diagonal finite-order unitary `D_ctl` whose eigenvalue on `|0^m>` is
`1` and does not occur on any other computational basis vector.  Put

```text
Delta=min_(z!=0^m)|lambda_z-1|>0.                     (ZER15)
```

Since `D_ctlG=G`, the one corner coefficient

```text
C_exit=(D_ctl W_game-W_game D_ctl)P_0Q                (ZER16)
```

satisfies

```text
C_exit=(D_ctl-I)W_gameG,
||C_exit||_2^2
 >=Delta^2||(I-P_0)W_gameG||_2^2
 >=Delta^2(1-rho^2)2^(-m)tau(Q).                      (ZER17)
```

Therefore the precise one-cell replacement for `(PAZ12)` is

```text
||(D_ctl W_game-W_game D_ctl)P_0Q||_2^2
 <=K E_rel+o(1).                                      (ZER18)
```

It is strictly weaker than forcing `W_gameP_0Q=P_0Q`: it only authenticates
that the verifier cannot exit the unique zero-control eigenspace.

## HALT and regular firewalls

In the exact perfect HALT witness, `W_gameG=G`, so `(ZER16)` vanishes.  If
the capacity source itself vanishes, the row is vacuous.  Thus `(ZER18)` does
not require a tracial extension and preserves the native mark.

The relation must remain a **capacity-gated corner** relation.  Imposing the
global word commutator `[D_ctl,W_game]=1` would constrain the verifier on its
whole representation and is not justified by the perfect Gram vector.

Nor does `(ZER18)` by itself give a universal trace inequality in the regular
representation.  The strict contraction `(ZER9)` is a finite-matrix game
statement; an exact infinite/non-CE representation may have a nonzero fixed
zero-control carrier.  A valid ordinary-group realization may therefore
name the single coefficient `(ZER16)` by a Hecke/Steinberg or proper-corner
cell and use a finite-dimensional-only kernel-reflection theorem.  It must
not replace the corner by a global commutator relator.

## Verdict

Pauli source control, support-menu packet types, exact half-edge ties, the
triangle two-cell, block-encoded verifier syntax, and the existing capacity
and reservoir commutator cells still admit `(ZER7)`.  The exact missing datum
is not another packet type or another triangle relation.  It is one mixed
acceptance/source corner:

```text
zero-control exit row `(ZER11)`,
equivalently the finite Pauli row `(ZER13)`,
or the single clock row `(ZER18)`.                     (ZER19)
```

Any one of these, with a matrix-only ordinary-word authentication, closes
`(PAZ12)`.
