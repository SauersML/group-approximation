---
rg: 2
id: two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
kind: claim
title: Two scale-changing selector rows with one gauge obey one affine rank parameter
distinct_from:
  shared-gauge-cz-cancellation-needs-an-identity-outer-anchor: that cancels one CZ gauge by an identity-outer occurrence; this retains the gauge and eliminates it by two incompatible source/target rank equations.
  controlled-fine-reflection-superrank-orientation-law: that computes the balanced orientation forced by one binary coarse-to-fine row; this gives the simultaneous two-row obstruction and the robust trace inequality.
  cyclic-coarse-fine-selector-rows-spread-carrier-error: that telescopes rank deficits around unrelated carriers and gauges; this uses two rows on one packet carrier and one common multiplicity involution.
---

**ESTABLISHED MATRIX THEOREM.**  Let `H` have dimension `n`, let `M` have
dimension `m>0`, and let `V=V^*=V^(-1)` on `M`.  Write

```text
theta=rank((1+V)/2)/m.
```

For a reflection `C_q=1-2F_q` on `H`, where `rank(F_q)=qn`, the negative
spectral fraction of

```text
T_q=C_q tensor V
```

is exactly

```text
Phi_q(theta)=q theta+(1-q)(1-theta)
            =1-q+(2q-1)theta.                         (TSG1)
```

Consequently, if a unitary selector row conjugates a source reflection with
negative fraction `r` to `T_q`, then

```text
r=Phi_q(theta).                                        (TSG2)
```

Two rows carrying the **same unitary-conjugacy class** of multiplicity
involution therefore have a finite-dimensional model only if their two
affine equations in the one unknown `theta` are compatible.  Literal equality
of the gauges is unnecessary; equality of their positive spectral ranks is
enough.  In particular the binary row

```text
(r_1,q_1)=(1/2,1/4)
```

forces `theta=1/2`, while the next-refinement row

```text
(r_2,q_2)=(1/4,1/8)
```

forces `theta=5/6`.  Hence no nonzero finite matrix carrier supports both
rows with one gauge.

The statement is robust.  In a normalized tracial matrix carrier, let
`R_i=1-2E_i` have `tau(E_i)=r_i`, let `C_i=1-2F_i` have
`tau_H(F_i)=q_i`, and put `T_i=C_i tensor V`.  For arbitrary unitaries
`W_i`,

```text
|r_i-Phi_(q_i)(theta)|
 <= (1/2)||W_i R_i W_i^*-T_i||_2.                     (TSG3)
```

Thus the distance between the two forced values of `theta` gives a
dimension-independent lower bound on the sum of the two selector-row
defects.  More precisely, suppose the two forced values

```text
theta_i^*=(r_i-(1-q_i))/(2q_i-1)
```

belong to `[0,1]`, put `c_i=2|2q_i-1|`, and write
`Delta=|theta_1^*-theta_2^*|`.  Then `(TSG3)` gives the three sharp
consequences

```text
delta_1+delta_2
  >= min(c_1,c_2) Delta,                              (TSG4a)

delta_1^2+delta_2^2
  >= (c_1^2 c_2^2/(c_1^2+c_2^2)) Delta^2,            (TSG4b)

max(delta_1,delta_2)
  >= (c_1 c_2/(c_1+c_2)) Delta.                       (TSG4c)
```

The constants are optimal consequences of the two scalar rank inequalities.
For the two binary rows above, writing

```text
delta_i=||W_i R_i W_i^*-T_i||_2,
```

`(TSG3)` gives explicitly

```text
delta_1 >= |theta-1/2|,
delta_2 >= (3/2)|theta-5/6|,

delta_1+delta_2 >= 1/3,
delta_1^2+delta_2^2 >= 1/13=13/169,
max(delta_1,delta_2) >= 1/5.                          (TSG5)
```

In particular one of the two row defects is at least `1/5`.  No density
bound, spectral choice, PI degree, or property `(T)` is used after the common
carrier and common gauge have been decoded.

The same obstruction tolerates an approximately shared gauge.  Let the two
rows use multiplicity involutions `V_1,V_2`, and put

```text
theta_i=tau((1+V_i)/2),
epsilon_g=||V_2-SV_1S^*||_2
```

for a multiplicity-space unitary `S`.  Then

```text
|theta_1-theta_2| <= epsilon_g/2,

delta_1+(2/3)delta_2+(1/2)epsilon_g >= 1/3.           (TSG6)
```

Consequently

```text
delta_1^2+delta_2^2
 >= (9/13)(1/3-epsilon_g/2)_+^2.                     (TSG7)
```

If the gauge error tends to zero, `(TSG7)` recovers the local `1/13` floor.
On a reducing carrier of ambient trace `beta`, the corresponding ambient
squared row energy is at least `beta/13-o(1)`.  The value `1/104` follows
only if the **same authenticated row carrier** has `beta>=1/8-o(1)`; a
separate trace-`1/8` marked overlap does not by itself authenticate either
native selector occurrence.

This produces a new finite-coordinate compiler target for the binary
Leavitt route.  It is strictly weaker than manufacturing a literal fine
reflection or an identity-outer anchor: expose two scale-changing rows on
one carrier and prove only that their Clifford groupifications have conjugate
external involutions.  Existing packet dressing does not do this.  By
`packet-dressed-shared-implementer-requires-one-outer-class`, it shares a
gauge only within one outer-automorphism class, whereas the two unequal-rank
selector actions are not supplied as dressings of one fixed Pauli outer
class.  A successful construction must therefore use a genuine mixed
Leavitt two-cell or recursive tail holonomy, not an internal Clifford word.

The established cross-Gram lemmas fit this weaker endpoint exactly.  A fixed
positive cross-Gram moment between the two packet transports yields a fixed
positive reducing polar subcorner by
`two-transport-cross-gram-has-a-fixed-mass-reducing-corner`; the two mixed
Pauli commutators of
`two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge` place that
relative polar unitary in the smaller reservoir.  Unlike the invalidated mutual-bicommutant
route, the present argument needs no joint-fullness or spectator-elimination
theorem: tensoring both gauges by an unused identity leaves `theta` and
`(TSG4)` unchanged.  The remaining scalar target is therefore any fixed
positive cross-Gram overlap for the two native scale-changing transports.
