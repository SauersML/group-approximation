---
rg: 2
id: commuting-raw-qutrit-router-rank-ceiling-proof
kind: route
title: Separate the active rank from the qutrit character and optimize the rectangular gauge
target: commuting-raw-qutrit-router-has-active-rank-ceiling
requires:
  - jacobson-sign-polar-ranks-are-five-over-72-and-one-over-16
  - three-carrier-hidden-line-join-crosses-target-but-has-no-range
---

## 1. The 288-dimensional head splits into a qutrit line and an active factor

Use the notation of the exact sign-rank calculation.  The finite head is

```text
F_0=<C,H,C_1,W>
   isomorphic to <h> times K,
K=<H> times (A semidirect <k>),               |K|=96.   (CRQ5)
```

Here `C=<h> times <k>`, `|h|=|k|=3`, and `A isomorphic to F_2^4`.
Let `f_j` be the three character projections of `<h>`.  The selected
qutrit atoms have the form

```text
e_a=f_(2+a)e_k.                                          (CRQ6)
```

Let `P_sigma` be the relevant initial or range polar support of
`G_(sigma,+)e_k` in the regular representation of `K`.  The
Frobenius-group count in the sign-rank theorem says

```text
rank_K(P_+)=10,                    rank_K(P_-)=9.         (CRQ7)
```

Indeed, adjoining the two selected `h`-character blocks gives ranks
20 and 18 in the regular representation of `F_0`, which are exactly
the numerators of `5/72` and `1/16`.

The active part of the target is

```text
Q_act=E e_k.
```

The two factors `E` and `e_k` have regular traces `1/2` and
`1/3`, so

```text
rank_K(Q_act)=96/(2*3)=16.                               (CRQ8)
```

Thus the source crossing in the previous theorem is entirely a
two-character effect:

```text
2 rank(P_+)=20>16,             2 rank(P_-)=18>16,        (CRQ9)
```

while a single target-character slice of the same active polar has rank
only 10 or 9.

## 2. Every commuting parallel raw packet has the same ceiling

Take finitely many literal elementary roots with coefficients `S` or
`T` whose matrix directions are product-zero.  Write their off-diagonal
parts as `L(v)`.  Then

```text
L(v)L(w)=0,
(1+L(v))(1+L(w))=1+L(v+w).                              (CRQ10)
```

After closing under the finite qutrit orbit, their group `N` is a
finite elementary abelian 2-group.  This statement does not replace the
raw coefficient by `ST`: the entries can still be literal `S` and
`T`.  Finiteness follows because no directed product of two entries is
available.

Choose the root positions in unused multiplicity blocks, as in the
commuting moved-root construction.  Then `K` commutes with `N`;
`h` may act on `N`, and `k` acts trivially on the chosen
intertwiner packet.  The complete local group is therefore

```text
L=(N semidirect <h>) times K,                  |L|=288|N|. (CRQ11)
```

Now let `B` be any operator in the local complex group algebra whose
right support is contained in the two source-character block and whose
left support is contained in one target-character block while preserving
the active polar:

```text
B=B(f_0+f_2)P_sigma,             B=f_1P_sigma B.         (CRQ12)
```

This includes every full-`C` Fourier coefficient made from the
commuting raw packet, arbitrary finite linear combinations of such
coefficients, and their products with the three-line selector on the
active factor.

If `R_B` is the range projection of the polar of `B`, then the
second equality in `(CRQ12)` gives

```text
R_B<=f_1P_sigma.                                        (CRQ13)
```

The canonical trace on the direct product in `(CRQ11)` factors.  The
coefficient of the identity in every `f_j` is `1/3`, independently
of the action of `h` on `N`.  Hence

```text
tau_L(f_1P_+)= (1/3)(10/96)=5/144,
tau_L(f_1P_-)= (1/3)( 9/96)=1/32.                       (CRQ14)
```

Equations `(CRQ13)--(CRQ14)` prove the universal ceiling.  Enlarging
`N`, removing its trivial-character quarter kernel, arranging
orthogonal Fourier phases, or proving a singular-value lower bound
cannot change it.  The factor `|N|` cancels from normalized rank.

The full target is `f_1Q_act=Ee_2), with trace `16/288=1/18).
The exact remaining deficits are

```text
16/288-10/288=6/288=1/48,
16/288- 9/288=7/288.                                    (CRQ15)
```

For `N isomorphic to F_2^(2m)`, equation `(CRQ11)` gives the
explicit finite absorber order `288*4^m`.  Thus even arbitrarily many
parallel raw orbit copies cannot solve the range problem.  A surviving
raw word must change the active polar, which means touching an active
sign coordinate or making a nonzero mixed `S/T` composition.

## 3. The exact unconstrained rectangular optimizer

The preceding ceiling is sharp for its commuting hypothesis, not a
general dimension obstruction.  Work now in the 288-dimensional regular
head space itself.  Put

```text
P=(f_0+f_2)P_sigma,                 Q=f_1Q_act=Ee_2.      (CRQ16)
```

The two summands `f_0P_sigma` and `f_2P_sigma` have equal ranks
`r=10` or `r=9`, while `rank(Q)=16`.  Choose subprojections

```text
P_0<=f_0P_sigma,          P_2<=f_2P_sigma,
rank(P_0)=rank(P_2)=8,          P_sel=P_0+P_2.           (CRQ17)
```

Choose a partial isometry `V` from `P_sel` onto `Q`.  Extend it
to a unitary `U` so that

```text
U(P-P_sel)U^*<=1-Q.                                    (CRQ18)
```

This is possible by extending orthonormal bases.  The excess source
dimension is only `2r-16`, namely 4 or 2.  Equation `(CRQ18)` gives

```text
T=QUP=UP_sel=V,
T^*T=P_sel,                    TT^*=Q.                  (CRQ19)
```

All nonzero singular values of `T` are exactly one.  Therefore

```text
tau(T^*T)=tau(TT^*)=16/288=1/18,                        (CRQ20)
```

and the discarded source traces are

```text
(20-16)/288=1/72,                (18-16)/288=1/144.      (CRQ21)
```

The two branches `T_a=T f_a` have orthogonal rank-eight initial and
range spaces.  Since `T_a=Ee_2 T_a e_a`, they obey exact full-`C`
source and target typing.  Thus full Fourier typing, full target range,
trace `1/18`, and a dimension-free polar modulus can all coexist in
one finite-dimensional matrix model.  What is missing is an algebraic
reason for the particular rank-eight choices in `(CRQ17)`.

## 4. Why the optimizer does not authenticate a Lin occurrence

Let `p` be any projection in a tracial occurrence algebra.  Tensoring
`(CRQ19)` with `p` gives

```text
(T tensor p)^*(T tensor p)=P_sel tensor p,
(T tensor p)(T tensor p)^*=Q tensor p.                  (CRQ22)
```

The occurrence projection appears unchanged on both sides.  The exact
part of the named source which was discarded has trace

```text
tau((P-P_sel) tensor p)=
  (1/72)tau(p)                 for sigma=+,
  (1/144)tau(p)                for sigma=-.             (CRQ23)
```

Consequently declaring `P_sel tensor p` to be the source after the
polar is tautological; it does not preserve the established larger
three-line source.  Conversely, demanding initial support
`P tensor p` fails by the positive amount in `(CRQ23)`.

More importantly, the target in `(CRQ22)` is still `Q tensor p`.
Every noncommutative relation carried by the Lin occurrence remains in
the multiplicity factor; no degree-two tuple has been identified with a
degree-four tuple in the finite head.  Orthogonal conditioning by a Lin
PVM merely makes `(CRQ22)` block diagonal.

The remaining search target is therefore exact.  One needs a bounded
mixed raw return which

1. does not commute with the active 96-dimensional sign factor;
2. selects, in a representation-independent way, two rank-eight source
   pieces whose sum is the named occurrence support; and
3. removes rather than transports the Lin multiplicity while retaining
   a uniform polar modulus.

Neither parallel raw Fourier modes nor an unconstrained safe rectangular
orientation supplies these three statements.  No nonhyperlinearity
conclusion is claimed.
