---
rg: 2
id: native-inverse-pair-orbit-free-holonomy-proof
kind: route
title: Compute the literal row-one inverse-pair orbits and their finite moving-chart holonomy model
target: native-inverse-pair-seven-orbits-retain-external-gauge
requires:
  - native-whitehead-hecke-head-has-order-seven-anchor
  - nested-inverse-pair-returns-signed-source-with-free-sign
---

Work in `EL_20(L_(F_2)(1,2))` and retain the row-one words

```text
J=J_1,
T=J_1B_2A_1,
u=x_75(t_0),
v=x_56(s_0),
a=x_97(1).
```

The native calculation gives `J^2=T^7=1`.  Direct faithful-prefix
multiplication gives

```text
JuJ=x_75(s_1t_(01)) x_85(e_(00)),
(Ju)^2=x_75(s_0t_(00)) x_85(e_(00)).                 (NIO1)
```

Thus the first literal Whitehead occurrence is not a return to the signed
source.  The complete Singer orbit is just as explicit.  Put

```text
r=x_75(s_1t_(01)).
```

For every `j=1,...,6`, faithful-prefix matrix multiplication gives

```text
(T^j u)^7=r.                                         (NIO2)
```

Since

```text
(s_1t_(01))s_0=s_1t_1=q_1,
```

the first returned continuation of `(NIO2)` is

```text
[a,[r,v]]=x_96(q_1).                                 (NIO3)
```

The full signed-`L_0` conjugation test fails for `x_96(q_1)`.  Hence
`(NIO2)` does not return the native odd occurrence to the full signed
source; the two commutators needed in `(NIO3)` also use the Singer residual
with even occurrence parity.

There is a stronger adjacent inverse-pair menu.  Define

```text
p=x_97(t_0),                 q=x_76(s_0).
```

Then

```text
[p,q]=x_96(t_0s_0)=x_96(1)=n.                        (NIO4)
```

Both individual letters have exact odd Singer norm relations.  Their
seven `T`-conjugates, written as commuting root packets, have coefficient
supports

```text
p:  t_0;
    t_(00);
    t_1+t_0;
    t_1;
    t_1+t_(00);
    t_0+t_(00);
    t_1+t_0+t_(00),

q:  s_0;
    s_1+s_0+s_(00);
    s_0+s_(00);
    s_1+s_(00);
    s_1;
    s_1+s_0;
    s_(00).                                           (NIO5)
```

Each of the three displayed prefix monomials occurs four times.  All roots
within either row of `(NIO5)` commute, and the coefficient field has
characteristic two.  Therefore both forward and reverse norms are one:

```text
product_(k=0)^6 T^k p T^(-k)=1,
product_(k=6)^0 T^k p T^(-k)=1,
product_(k=0)^6 T^k q T^(-k)=1,
product_(k=6)^0 T^k q T^(-k)=1.                      (NIO6)
```

The tempting collection argument also has an exact obstruction.  Write
`p_k=T^kpT^(-k)` and `q_l=T^lqT^(-l)`.  Every cross commutator is either
one or the *same* external root `n=x_96(1)`.  With `1` denoting `n`, its
complete exponent table is

```text
1 1 1 0 0 1 0
0 1 1 1 0 0 1
1 0 1 1 1 0 0
0 1 0 1 1 1 0
0 0 1 0 1 1 1
1 0 0 1 0 1 1
1 1 0 0 1 0 1.                                     (NIO7)
```

Each row has weight four.  The diagonal has weight seven, but the
off-diagonal has weight twenty-one.  Collecting the two norm-one products
therefore gives only

```text
n^(7+21)=n^28=1,                                     (NIO8)
```

which is tautological for an involution.  The twenty-one nonzero
off-diagonal entries are literally `n`, not positive signed-`L_0` roots.
Consequently a same-representation carrier cannot declare them trivial
while retaining the seven diagonal copies of that same group element.

Equations `(NIO4)--(NIO8)` are genuine odd-occurrence relations, but they
constrain only cyclic products of the seven moving stage gauges.  The
following exact finite model shows that they do not identify the returned
gauge with one chosen native transition gauge.

Let

```text
H=C^7_stage tensor C^2_D tensor C^8_label tensor C^2_E.
```

On the three-bit label use the third power of the order-seven matrix

```text
M=[[1,1,0],[1,1,1],[0,1,0]] in GL_3(F_2).
```

Let `T` shift the seven-stage coordinate, act by `M^3` on the label, and
insert `D=Z` on each of the first two stage edges.  Then `T^7=1`: the
label action has order seven and the moving-stage holonomy is `D^2=1`.
On the `E=-1` block let `P=X_(e_1)` and `Q=Z_(e_1)` on the three-bit
label; on the `E=+1` block let both be one.  The nonzero `M`-orbit and
dual `M^(-transpose)`-orbit each sum to zero, so the forward and reverse
seven-orbit products of `P` and `Q` are one.  Their commutator is exactly

```text
[P,Q]=E=I-I_(E=-1)*2.                                 (NIO9)
```

The transition reflection `D=Z_D` and returned reflection `E=Z_E` act on
different tensor factors.  They commute, are distinct, and `DE` is
nontrivial.  This is a `224`-dimensional exact unitary model of
`T^7=1`, all four relations `(NIO6)`, the complete cross table `(NIO7)`,
`(NIO4)` at the gauge level, and
`[T,E]=1`, while the native and returned signs remain independent.

For completeness, the literal `u,v,J,T` minimal menu also has a
`112`-dimensional signed-permutation moving-chart model.  A local `J`
swap and the first two `T` edges carry `D`; two Pauli involutions on an
independent returned block have commutator `H`, and a chart swap `A`
satisfies `[A,H]=E`.  It realizes `J^2=T^7=1`, `[J,v]=[T,v]=1`,
`[J,E]=[T,E]=1`, and both the original and Singer-residual nested return
patterns with `D != E`.  The accompanying MSI artifact checks this model
as signed permutations rather than relying on a diagrammatic assertion.

Thus neither the literal one-Whitehead interaction, the direct Singer
orbit of `u`, nor even the two exact odd norm relations `(NIO6)` supplies a
same-chart equation `D=E`.  A successful continuation must type at least
one intermediate nonnormal conjugate on a common reducing carrier, rather
than use only its cyclic norm or terminal commutator.

No Property `(T)`, trace input, literature theorem, local computation, or
Lean compilation is used.
