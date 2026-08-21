---
rg: 2
id: graph-commutator-authenticates-paz-return
kind: claim
title: A graph commutator authenticates the sole Pauli zero-atom return moment
distinct_from:
  pauli-zero-atom-removes-acceptance-source-deficit: that isolates the PAZ12 return scalar after removing source loss; this converts that scalar into one authenticated commutator mark on a fixed amplification.
  mixed-pauli-commutator-authenticates-one-capacity-cut: that treats leakage of an involution spectral cut under one covariance involution; this treats the internal return phase and range leakage of an arbitrary verifier unitary.
  authenticated-pauli-branch-needs-source-saturation: that proves the sharp two-child trace recurrence and its stationary Pauli countermodel; this composes that recurrence with the newly authenticated PAZ return mark.
---

Work after the fixed Pauli-control exactification of
`pauli-zero-atom-removes-acceptance-source-deficit`.  Put

```text
G=P_0Q,                                                 (PAG1)
eta=eta_0(Q)
   =tau(G)-Re tau(GW G),                                (PAG2)
```

where `G` is a projection and `W=W_game` is unitary.  Since `G^2=G`,

```text
eta=1/2||(W-I)G||_2^2.                                 (PAG3)
```

The scalar `(PAG2)` is not a plain commutator with `G`: if `W` reduces `G`
but acts there by a nontrivial phase, `[W,G]=0` while `eta>0`.  A fixed graph
amplification repairs exactly this defect.

## Graph projection and return commutator

Pass first to `M_2(M)` with normalized trace `tau_2`.  Let

```text
p_+=1/2 [[1,1],[1,1]],
R=p_+ tensor G,
U=diag(I,W),
X_R=2R-I.                                               (PAG4)
```

Thus `R` is the graph/diagonal copy of the source `G`, `U` compares the
identity return with the game return, and `X_R` is its reflection.

Pass once more to `M_2(M_2(M))` and define two self-adjoint unitaries

```text
A=diag(X_R,X_R),
B=[[0,U^*],[U,0]],
C=ABAB.                                                 (PAG5)
```

The unitary `C` is the commutator of the two involutions `A,B`.  It is the
authenticated return coordinate.

### Theorem 1 — exact comparison

Put

```text
b=||(I-G)WG||_2^2.                                     (PAG6)
```

Then exactly

```text
||C-I||_2^2=2 eta+b,                                   (PAG7)
0<=b<=2 eta,                                           (PAG8)
```

and therefore

```text
2 eta<=||C-I||_2^2<=4 eta.                             (PAG9)
```

Equivalently,

```text
1/4||C-I||_2^2<=eta<=1/2||C-I||_2^2.                  (PAG10)
```

### Proof

Let

```text
L=||(I-R)UR||_(2,tau_2)^2.                             (PAG11)
```

The compression of `U` to the graph range is

```text
RUR  is unitarily equivalent to  G(I+W)G/2.
```

A direct normalized-trace calculation gives

```text
L=eta/4+b/8.                                           (PAG12)
```

For completeness, if `s=tau(G)`, `r=Re tau(GWG)`, and
`a=||GWG||_2^2`, then

```text
eta=s-r,
b=s-a,
L=(3s-2r-a)/8.
```

The two off-diagonal blocks of `U` relative to `R` have equal HS norm, so

```text
||[U,R]||_2^2=2L.                                      (PAG13)
```

Since `X_R=2R-I`, and the two diagonal blocks of the commutator in `(PAG5)`
have the same HS norm,

```text
||C-I||_2^2
 =||X_RUX_RU^*-I||_(2,tau_2)^2
 =4||[U,R]||_(2,tau_2)^2
 =8L.
```

Together with `(PAG12)` this is `(PAG7)`.  Finally,

```text
b=||(I-G)(W-I)G||_2^2
 <=||(W-I)G||_2^2=2eta,
```

which proves `(PAG8)--(PAG10)`.  ∎

Thus PAZ12 is not an arbitrary positive coefficient.  On a fixed
four-fold ancillary amplification it is, up to universal factors `1/4` and
`1/2`, the distance of one commutator of two involutions.

## Authenticate the commutator by one involution mark

Introduce a central involution `Y` and the mixed relation

```text
r_mix=Y^(-1)C.                                         (PAG14)
```

When `r_mix=I`, relation `(PAG10)` gives

```text
eta<=1/2||Y-I||_2^2=2 tau(P_Y),
P_Y=(I-Y)/2.                                           (PAG15)
```

For an approximate mixed relation, with `Y` already rounded to an
involution,

```text
eta
 <=||Y-I||_2^2+||r_mix-I||_2^2
 =4tau(P_Y)+||r_mix-I||_2^2.                           (PAG16)
```

Indeed `(PAG10)` gives `eta<=||C-I||_2^2/2`, and

```text
||C-I||_2<=||C-Y||_2+||Y-I||_2
           =||r_mix-I||_2+||Y-I||_2.
```

This is the PAZ analogue of mixed Pauli authentication: an independent root
factor can no longer declare zero defect while the state-local return lives
on another reservoir.

The reflection `X_R` is a fixed finite Hecke expression in the graph ancilla
and the commuting projection `G=P_0Q`; `B` is the standard involutive
dilation of the controlled word `U`.  Turning those two fixed expressions
into ordinary words is a finite packet/naming problem and is deliberately
separate from the analytic statement proved here.

## Composition with the sharp two-child recurrence

Assume a finite-matrix decoder supplies contractions `S_0,S_1` and
orthogonal child tags `B_0,B_1<=P_Y` with

```text
alpha_i=||S_i^*S_i-P_Y||_2,
lambda_i=||(I-B_i)S_i||_2.                             (PAG17)
```

The recurrence in
`authenticated-pauli-branch-needs-source-saturation` gives

```text
tau(P_Y)
 <=tau(P_Y)/2
   +(alpha_0+alpha_1+lambda_0^2+lambda_1^2)/2,
```

hence

```text
tau(P_Y)
 <=alpha_0+alpha_1+lambda_0^2+lambda_1^2.              (PAG18)
```

Combining `(PAG16)` and `(PAG18)` yields the dimension-independent upper
bound

```text
eta_0(Q)
 <=4(alpha_0+alpha_1+lambda_0^2+lambda_1^2)
   +||r_mix-I||_2^2.                                   (PAG19)
```

Under the exact mixed relation, the sharper `(PAG15)` gives

```text
eta_0(Q)
 <=2(alpha_0+alpha_1+lambda_0^2+lambda_1^2).           (PAG20)
```

Thus PAZ12 is analytically discharged once the two child source moments and
range leakages are paid by defining word energy.  No further acceptance
moment remains.

## Exact completeness firewall

In the perfect witness,

```text
WG=G.
```

Therefore `eta=b=0`, `C=I`, and the mixed cell extends with `Y=I`.  Then
`P_Y=0`, so the two-child return cell is vacuous.  The original native mark
on the multiplicity factor is unchanged.  No global relation `W=I` is
imposed.

This is strictly better than a global commutation relation: it tests only
the graph of the actual state-local source `G`.

## Exact stationary countermodel to the unsaturated return

The authenticated mark and two inherited child tags still do not prove
`(PAG18)` without source saturation.

Take the smallest exact model

```text
G=I,
W=-I.                                                   (PAG21)
```

Then `eta=2`, `b=0`, and `(PAG7)` gives

```text
C=-I,
Y=-I,
P_Y=I.                                                  (PAG22)
```

Tensor with a second Pauli pair `X_2,Z_2` having the same central
commutator `Y`, and take

```text
B_+=(I+X_2)/2,
B_-=(I-X_2)/2.                                          (PAG23)
```

Both orthogonal children carry the same authenticated `Y=-I` packet and
sum to `P_Y`, but each has half the parent trace.  The zero-error recurrence

```text
tau(P_Y)<=[tau(B_+)+tau(B_-)]/2
```

fails as `1<=1/2`.  This exact finite rectangular/stationary model satisfies
the graph authentication and every child invariance/orthogonality relation.
It violates precisely the two full-source moments in `(PAG17)`.

## Regular-trace firewall

If the saturated self-return relations in `(PAG17)` were imposed as
universal operator identities inside the group von Neumann algebra, then
`(PAG18)` at zero error would force `P_Y=0` and `Y=I` in the faithful regular
representation.  Hence they cannot be universal tracial Leavitt relations.

The source moments must arise only after finite-dimensional packet
multiplicity decoding.  A properly infinite exact representation may use
the Cuntz/Hilbert-hotel completion from
`authenticated-pauli-branch-needs-source-saturation`; the perfect PAZ
witness itself uses the vacuous `P_Y=0` branch.

## Attempts

- **Use `[W,G]` as the mark.**  It misses internal action of `W` on `GH`;
  `W` may reduce `G` and still have `eta>0`.  The graph projection records
  both internal phase and range leakage, producing `(PAG7)`.
- **Use only one Hadamard-test ancilla.**  It turns `eta` into one rejected
  transition probability but does not yield an involution commutator mark.
  The second fixed dilation in `(PAG5)` makes both generators involutions.
- **Apply the two-child recurrence from inheritance alone.**  The exact model
  `(PAG21)--(PAG23)` survives.  Both child source moments are load-bearing.
- **Impose saturated return universally.**  The regular-trace argument kills
  `Y` algebraically.  Saturation must be matrix-coordinate only.

## Verdict

The sole analytic PAZ12 moment admits a complete one-coordinate
authentication:

```text
eta_0(Q)
 comparable_to ||[A,B]-I||_2^2
 -> one involution root Y.                              (PAG24)
```

Together with the proved two-child recurrence this gives the explicit upper
bound `(PAG19)`.  The only unproved group interface is now the same pair of
finite-dimensional source-saturation moments isolated previously.  Without
them, `(PAG21)--(PAG23)` is an exact stationary countermodel to every current
analytic relation.
