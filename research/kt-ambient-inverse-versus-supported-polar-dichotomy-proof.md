---
rg: 2
id: kt-ambient-inverse-versus-supported-polar-dichotomy-proof
kind: proof
title: One ambient Laurent inverse row shatters the optimal KT collision carrier
proves:
  - kt-one-laurent-inverse-row-shatters-collision-support
requires:
  - kt-canonical-lamp-collision-forces-vanishing-intertwiner
  - kt-intermediate-actor-cannot-extract-positive-coefficient-transport
---

# One ambient Laurent inverse row shatters the optimal KT collision carrier

## 1. Collision support and an inverse candidate

Use a rank-`r` collision packet as in the canonical lamp theorem. Let
`T in M_d` be a partial isometry, put `P=T^*T`, and suppose

~~~text
q=tau(P)
 <=alpha_r:=2^(-r)+(1-2^(-r))epsilon+r^2 delta^2.           (1)
~~~

Here `epsilon` is the nontrivial collision-character bound and `delta`
is the lamp-transport covariance error.

Let `R` be any contraction proposed as the reverse Laurent transport.
Since

~~~text
rank(RT)<=rank(T)=qd,
~~~

the Eckart--Young rank bound gives

~~~text
||RT-I||_2^2>=1-q.                                        (2)
~~~

The same argument gives `||TR-I||_2^2>=1-q`. Combining with (1),

~~~text
min{||RT-I||_2^2,||TR-I||_2^2}
 >=1-2^(-r)-(1-2^(-r))epsilon-r^2 delta^2.                (3)
~~~

Thus in a canonical sequence with fixed `r` and vanishing trace and
covariance errors,

~~~text
liminf min{||RT-I||_2,||TR-I||_2}
 >=sqrt(1-2^(-r)).                                        (4)
~~~

The named pair `0,[y]` already gives the floor `1/sqrt(2)`. Letting
the fixed collision rank tend to infinity after the microstate limit makes
the floor tend to one.

## 2. The explicit full-Laurent row

The intermediate ring

~~~text
S=F_2[x_1,y,x_3]
~~~

does not contain `x_1^(-1)`. Adjoining it adds the coefficient identities

~~~text
x_1^(-1)x_1=1=x_1x_1^(-1).                                (5)
~~~

At the elementary-group level these appear in the explicit Steinberg rows

~~~text
[e_13(x_1^(-1)),e_32(x_1)]=e_12(1),
[e_13(x_1),e_32(x_1^(-1))]=e_12(1).                       (6)
~~~

Suppose an actor-to-carrier extraction sends multiplication by `x_1` to
`T`, multiplication by `x_1^(-1)` to `R`, and sends the unit in (5)
to the ambient identity. Then (5)--(6) require the left side of (3) to
tend to zero. Equation (4) rules this out.

Consequently **one** genuine Laurent inverse direction is enough to destroy
the shrinking collision carrier, provided the extracted carrier is unital
on the ambient physical space. No long moving word packet is needed after
that functoriality has been obtained.

## 3. The supported-polar escape is exact

The unitality clause is essential. In the exact finite collision model put

~~~text
T=E_r=2^(-r) product_(j=1)^r(I+z_0z_j),
R=E_r.
~~~

Then

~~~text
RT=TR=E_r=T^*T=TT^*.                                      (7)
~~~

Thus the two arrows are exact inverses in the supported corner, while

~~~text
||RT-I||_2=||TR-I||_2=sqrt(1-2^(-r)).                     (8)
~~~

This attains (3) with `epsilon=delta=0`. The full inverse relation can
therefore disappear completely after polar compression if it is recorded
only as

~~~text
RT=T^*T,            TR=TT^*                               (9)
~~~

rather than as the ambient identities in (5).

## 4. Exact remaining gate

The joint Fourier/rank linear program is solved by (3):

1. ambient unital inverse transport has a defect approaching one;
2. supported polar inverse transport is exactly satisfiable on the optimal
   `2^(-r)` carrier.

Hence the extra Laurent row does shatter the intermediate countermodel, but
only after an actor-to-carrier theorem proves **support completion**. It is
not enough to extract mutually inverse partial isometries in their own
corners; those are the sharp countermodel (7).

This isolates the full-Laurent seam without claiming it solved. A positive
KT argument must show that the unit word in (5), together with the canonical
lamp table and the full actor relations, is represented by the ambient
identity on the extracted carrier, equivalently that the polar support has
trace tending to one. The intermediate actor cannot supply that statement,
and (7) shows why.
