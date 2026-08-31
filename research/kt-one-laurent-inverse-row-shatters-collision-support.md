---
rg: 2
id: kt-one-laurent-inverse-row-shatters-collision-support
kind: claim
title: One full-Laurent inverse row shatters the KT collision carrier only after support completion
artifacts:
  - research/kt-ambient-inverse-versus-supported-polar-dichotomy-proof.md
distinct_from:
  kt-intermediate-actor-cannot-extract-positive-coefficient-transport: That gives the optimal shrinking-support carrier with all intermediate relations exact; this computes exactly what the first relation outside that actor does to the carrier.
  kt-no-denominator-window-balances-coefficient-and-canonical-inverse: That computes inverse rank in the concrete truncated-cone coefficient and additive carriers; this is representation-independent and applies to arbitrary canonical lamp microstates once a carrier transport has been extracted.
  kt-kazhdan-polar-compressor-rounding-is-directional: That produces supported partial intertwiners along one compressor; this proves supported inverse identities are insufficient and identifies ambient support completion as the missing clause.
---

**ESTABLISHED AMBIENT-VERSUS-SUPPORTED DICHOTOMY; SUPPORT COMPLETION IS OPEN.**

Let `T` be a partial transport for a rank-`r` canonical lamp collision
packet, with character error `epsilon` and covariance error `delta`.
The collision Fourier theorem gives

~~~text
q=tr(T^*T)
 <=2^(-r)+(1-2^(-r))epsilon+r^2 delta^2.                  (LID1)
~~~

For every contraction `R` proposed as the reverse transport,

~~~text
min{||RT-I||_2^2,||TR-I||_2^2}
 >=1-2^(-r)-(1-2^(-r))epsilon-r^2 delta^2.                (LID2)
~~~

This is just the rank bound `rank(RT),rank(TR)<=qd`, but it has a sharp
KT consequence. Adjoining `x_1^(-1)` to the intermediate coefficient ring
adds the explicit full-Laurent identities

~~~text
x_1^(-1)x_1=1=x_1x_1^(-1),
~~~

encoded by the Steinberg rows

~~~text
[e_13(x_1^(-1)),e_32(x_1)]=e_12(1),
[e_13(x_1),e_32(x_1^(-1))]=e_12(1).                       (LID3)
~~~

If an actor-to-carrier extraction sends multiplication by `x_1` and its
inverse to `T,R` and sends the unit in (LID3) to the **ambient** identity,
then (LID2) gives a defect floor `sqrt(1-2^(-r))`. The named
`0,[y]` pair already gives `1/sqrt(2)`; the infinite fixed kernel makes
the floor tend to one. Thus a single genuine Laurent inverse direction
shatters the shrinking collision carrier once ambient unitality is known.

The alternative is exact. For

~~~text
E_r=2^(-r) product_(j=1)^r(I+z_0z_j),
T=R=E_r,
~~~

all collision covariances hold and

~~~text
RT=TR=E_r=T^*T=TT^*,
tr(E_r)=2^(-r).                                           (LID4)
~~~

Hence the arrows are perfect inverses in their supported corner, and their
ambient inverse defect attains equality in (LID2).

The first full-Laurent row therefore does not leave an unclassified
countermodel: the joint Fourier linear program has exactly two outcomes.

1. Ambient unital transport: defect tends to one.
2. Supported polar transport: relations remain exact while support shrinks
   as `2^(-r)`.

The live theorem is now support completion. One must prove from the full KT
actor plus canonical lamp relations that the extracted polar unit is the
ambient identity, or at least has trace bounded below independently of
`r`. Merely producing forward and backward partial intertwiners, even
exact inverses on their supports, is refuted by (LID4).

DERIVATION
kt-ambient-inverse-versus-supported-polar-dichotomy-proof
