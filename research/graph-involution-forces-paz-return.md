---
rg: 2
id: graph-involution-forces-paz-return
kind: claim
title: A graph involution kills a strictly compressed projection source
distinct_from:
  graph-commutator-authenticates-paz-return: that compares a projection return with one graph commutator and then routes its involution mark into a branching recurrence; this proves that involutivity plus strict compression kills the projection source.
  pauli-zero-atom-removes-acceptance-source-deficit: that gives a positive-norm zero-control Gram vector and isolates PAZ12; this theorem needs a positive-density projection source and therefore does not by itself supply PAZ12.
  controlled-reflection-cell-has-free-orientation: that finds a finite controller orientation obstruction before the intended block compression is obtained; this works after those orientation moments have supplied the intended strict compressor.
---

**Type correction.**  The theorem below is correct for an orthogonal
projection `G` on the same Hilbert space on which `W` acts.  PAZ currently
supplies only one vector `g=P_0Q` in the Gram Hilbert space.  As proved in
`paz-gram-vector-is-not-a-graph-projection`, its rank-one projection has
normalized trace `Theta_m(d^(-2))`, while the positive-density left-support
projection need not make the graph commutator involutive in the exact
perfect witness.  Consequently the application `(GIF24)` to PAZ is
conditional on a new positive-density graph-projection decoder; it does not
currently close PAZ12.

There is an exact bad-atom model for every finite cell surrounding PAZ12
**before** the graph-commutator relation is imposed.  At the projection
level, the mixed graph relation is strong enough: when its authenticated
coordinate is an involution, strict compression forces that projection
source to vanish.  Applying this statement to PAZ still requires the
positive-density projection promotion isolated above.

## The pre-graph bad-atom model

Choose a native separator assignment and give the private `O_D` sign the
wrong value for the `C_D` conjunction.  The other three contexts admit
compatible allowed extensions by
`fanizza-native-additive-incidence-is-one-triangle`.  Realize the forbidden
`C_D` character in a finite induced packet representation and let `q_bad` be
its nonzero atom.  Put

```text
Q=I_ctl tensor q_bad tensor I_edge.                    (GIF1)
```

Use the intended controller orientations `u_j=I`, the selected Pauli spin
type, the support-menu packet types on an orthogonal summand, and the exact
half-edge/triangle representation from
`private-gauges-close-fanizza-triangle`.  Order the rejecting `C_D` test
first.  Then

```text
Q_1Q=0,
T_gameQ=0,
P_0W_gameP_0Q=0,                                      (GIF2)
```

so, for `G=P_0Q`,

```text
eta_0(Q)=||G||_2^2=2^(-m)tau(Q)>0.                    (GIF3)
```

All capacity and reservoir commutator locks can have zero defect: the bad
atom reduces every finite truth reflection, all relative multiplicity gauges
may be the identity, and the incidence-private factors are independent.
Thus none of those cells implies PAZ12.  The graph cell would be the first
relation coupling the return to one involutive mark if this vector source
could be promoted to the required positive-density graph projection.

## Graph notation

Work in a finite tracial matrix algebra `(M,tau)`.  Let `G` be a projection,
`W` a unitary, and assume the PAZ zero-control compression satisfies

```text
||GWG||_(op,GH)<=rho<1.                                (GIF4)
```

If a PAZ projection decoder supplied `G` as a positive-density projection,
then `(GIF4)` would follow from the finite-game estimate and
`P_0W_gameP_0=P_0 tensor T_game`.  The current Gram vector does not itself
supply this `G`.

In `M_2(M)` put

```text
R=p_+ tensor G,
U=diag(I,W),
S=2R-I.                                                (GIF5)
```

In one further `2 by 2` amplification put

```text
A=diag(S,S),
B=[[0,U^*],[U,0]],
C=ABAB.                                                (GIF6)
```

These are the objects of
`graph-commutator-authenticates-paz-return`.

## Exact collapse theorem

### Theorem

If there is a self-adjoint involution `Y` satisfying

```text
C=Y,                                                   (GIF7)
```

then

```text
G=0,
eta_proj(G)=0.                                         (GIF8)
```

### Proof

The two diagonal blocks of `C` are

```text
C_1=S U^* S U,
C_2=S U S U^*.                                        (GIF9)
```

Since `Y=Y^*`, `(GIF7)` makes `C_1` self-adjoint.  Both `S` and
`T=U^*SU` are involutions, and `C_1=ST`.  Self-adjointness gives

```text
ST=(ST)^*=TS.                                         (GIF10)
```

Thus the projections

```text
R,
R'=U^*RU                                               (GIF11)
```

commute.  Hence

```text
K=RR'R                                                 (GIF12)
```

is a projection on `RH`.

Identify `GH` isometrically with `RH` by

```text
Jxi=2^(-1/2)(xi,xi).                                   (GIF13)
```

Under this identification,

```text
K is unitarily equivalent to H^*H,
H=G(I+W)G/2.                                          (GIF14)
```

By `(GIF4)`,

```text
||H||_op<=(1+rho)/2<1.                                (GIF15)
```

But `H^*H` is a projection by `(GIF12)--(GIF14)`.  A projection of operator
norm strictly less than one is zero, so `H=0`.  On the other hand

```text
||Hxi||
 >=(1-rho)||xi||/2                 (xi in GH),         (GIF16)
```

again by `(GIF4)`.  Therefore `GH=0`, proving `(GIF8)`.  ∎

The centrality of `Y` is not used.  Its self-adjoint involution law and the
mixed equality `(GIF7)` are enough.

## Quantitative estimate

The same proof gives the required normalized-HS modulus.  Assume `Y=Y^*`
and `Y^2=I` exactly after the fixed involution rounding, and put

```text
epsilon=||C-Y||_2,
a=(1+rho)/2,
b=(1-rho)/2.                                           (GIF17)
```

Then

```text
||C-C^*||_2<=2epsilon.                                (GIF18)
```

For the first block this gives

```text
||[R,R']||_2<=epsilon.                                (GIF19)
```

Here a harmless fixed `sqrt(2)` block-normalization loss has been absorbed;
no assumption that the approximate `Y` is already block diagonal is needed.

With `K=RR'R`, the standard two-projection identity is

```text
tau_2(K-K^2)=1/2||[R,R']||_2^2<=epsilon^2/2.          (GIF20)
```

Equation `(GIF14)` and `(GIF4)` give

```text
b^2 R<=K<=a^2 R                                       (GIF21)
```

on the graph source in quadratic-form sense.  Since every spectral value of
`K` is at most `a^2<1`,

```text
(1-a^2)tau_2(K)<=tau_2(K-K^2).                        (GIF22)
```

Also `tau_2(K)>=b^2 tau(G)/2`.  Combining
`(GIF20)--(GIF22)` yields

```text
tau(G)
 <=epsilon^2/[b^2(1-a^2)].                            (GIF23)
```

Finally

```text
eta_proj(G)
 <=(1+rho)tau(G)
 <=K_rho epsilon^2,                                   (GIF24)

K_rho=4(1+rho)/[(1-rho)^2(1-(1+rho)^2/4)].
```

If `Y` is only approximately involutive, fixed spectral rounding adds the
corresponding fixed multiple of its involution defect.  Thus the ordinary
mixed relator energy `||C-Y||_2^2`, plus the finite `Y^2=1` defect, already
has the form required by PAZ12 once the missing positive-density projection
decoder is supplied.

## Correction to the stationary child countermodel

The exact stationary model

```text
G=I,
W=-I                                                     (GIF25)
```

from `graph-commutator-authenticates-paz-return` correctly shows that graph
authentication alone does not imply a generic two-child source recurrence.
It does **not** survive the conditional strict-compression hypothesis: its
compression has norm one, whereas `(GIF4)` has `rho<1`.  Therefore it is not
a countermodel to the projection-level theorem.

The branching/source-saturation problem remains relevant to other recurrent
lanes.  For PAZ, a positive-density coherent-frame or common-module source
is again needed before the projection-level theorem can be used.

## Firewalls

If an exact projection decoder has `WG=G`, then the graph commutator is
`C=I` and one may choose `Y=I`.  The PAZ perfect witness currently proves
this only for one vector, not for a positive-density projection.  Thus this
firewall is a required decoder clause rather than an established PAZ fact.

The proof does not force `Y=I` in the regular representation.  Its decisive
input is the strict finite-game compression `(GIF4)`, which is false for the
stationary regular model `(GIF25)` and need not hold in an exact non-CE
representation.  Thus the argument is finite-dimensional/game-specific and
does not create a universal tracial mark collapse.

## Conditional verdict

Before the graph relation, `(GIF1)--(GIF3)` is an exact finite countermodel to
all packet, half-edge, triangle, block-syntax, orientation, and independent
commutator cells.  After adding the already proposed ordinary mixed relation

```text
Y=ABAB,
Y^2=1,
Y=Y^*,                                                  (GIF26)
```

the displayed projection-level inputs force the graph source to vanish,
quantitatively by `(GIF24)`.  Promoting the PAZ Gram vector to such a
positive-density projection with an exact HALT extension is still open by
`paz-gram-vector-is-not-a-graph-projection`.  Therefore the current graph
cell does not yet prove PAZ12.
