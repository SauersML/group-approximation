# LXI: an explicit mixed Bell conjugate distinguishes Toeplitz and Cuntz shift tests

Date: 2026-09-05. Complete calculation for the stated test model.
This is a separate research artifact, not a route resolving LXI.

## 1. The concrete result

Let C=C(S^1)*_C T_2 be the full unital free product, write z for
the circle unitary, and let s_1,s_2 be the Toeplitz isometries.
Put

```text
p=s_1 s_1*,
e=1-s_1 s_1*-s_2 s_2*,
r=(s_1 z s_1 z* + s_2 z s_2 z*)/sqrt(2),
q=r r*.
```

There is an explicit unitary W in C with WpW*=q. In particular,
both q and 1-q are properly infinite and full. Consider the
Bernoulli shift quotient representations of C obtained by sending
z to the shift implementer and the Toeplitz generators to site
zero, first in tensor powers of T_2 and then in tensor powers
of O_2. For these two maps Phi_T and Phi_O, respectively,

```text
||[z,q]||_C = ||Phi_T([z,q])|| = 1,
||Phi_O([z,q])|| = sqrt(3)/2 < 1.
```

Thus a strict commutator estimate can occur in a quotient which
retains both proper-infinite isometries, even for an explicitly
liftable mixed unitary conjugate, without holding in the original
free product. The exact failure is caused by annihilating the
Toeplitz defect e. This test lies outside the MF coefficient
argument: it uses the actual isometries and their proper-infinite
witnesses throughout.

## 2. An actual unitary conjugating p to q

Orthogonality of s_1 and s_2 gives r*r=1. We now construct W
explicitly, so the argument does not appeal to unitary equivalence
deduced from K-theory.

For any unitary u in C define

```text
A(u)=e+s_1 u s_1*+s_2 u s_2*.
```

The ranges of s_1,s_2 are orthogonal and orthogonal to e, so A(u)
is a unitary and A(u)s_i=s_i u. Moreover, A is multiplicative on
unitaries. In particular,

```text
F=A(z A(z*))
```

is a genuine unitary in C.

Consider the two orthogonal families of four Toeplitz isometries

```text
a_1=s_1 s_1,       b_1=s_1,
a_2=s_2 s_2,       b_2=s_2 s_1,
a_3=s_1 s_2,       b_3=s_2 s_2 s_1,
a_4=s_2 s_1,       b_4=s_2 s_2 s_2.
```

Their missing range projections are, by successive expansion of
1=e+s_1s_1*+s_2s_2*,

```text
1-sum_i a_i a_i* = e+s_1 e s_1*+s_2 e s_2*,
1-sum_i b_i b_i* = e+s_2 e s_2*+s_2^2 e (s_2^2)*.
```

Define the coefficient unitary

```text
J=sum_(i=1)^4 a_i b_i*
  + e + s_1 e s_2* + s_2 e (s_2^2)*.
```

Each displayed term is a partial isometry. Their initial
projections are pairwise orthogonal and sum to one, as do their
range projections. Consequently J*J=JJ*=1, and Jb_i=a_i. In
particular Js_1=a_1.

Set t_i=F a_i. The identity A(u)s_i=s_i u gives the exact formulas

```text
t_1=s_1 z s_1 z*,  t_2=s_2 z s_2 z*,
t_3=s_1 z s_2 z*,  t_4=s_2 z s_1 z*.
```

For example,

```text
F s_i s_j = s_i z A(z*) s_j = s_i z s_j z*.
```

The t_i are therefore an orthogonal family of isometries. Let M
be the elementary unitary which applies the two-dimensional
Hadamard matrix to their first two ranges and is the identity on
the remaining complement:

```text
M=1-t_1t_1*-t_2t_2*
  +(t_1t_1*+t_1t_2*+t_2t_1*-t_2t_2*)/sqrt(2).
```

Then Mt_1=(t_1+t_2)/sqrt(2). Hence

```text
W=MFJ
```

is a unitary and Ws_1=r, proving WpW*=q. All formulas hold in
the original full free product with the nonzero Toeplitz defect;
they are not formulas valid only after passing to O_2.

Since p is equivalent to the unit and 1-p contains s_2s_2*,
both p and 1-p are properly infinite and full. The same is true
of q and 1-q by the explicit conjugation.

## 3. The two shift representations

For D equal to T_2 or O_2, let

```text
B_D=tensor_(n in Z) D,
E_D=B_D crossed_product_shift Z.
```

The tensor product is the unital minimal tensor-product inductive
limit over finite intervals. Write iota_n for the site inclusion,
and U_D for the implementing unitary with
U_D iota_n(d) U_D*=iota_(n+1)(d). The universal property gives
a unital homomorphism Phi_D:C -> E_D by sending z to U_D and
s_i to iota_0(v_i), where v_i are the canonical generating
isometries of D. For D=O_2 this includes the usual quotient
T_2 -> O_2.

The finite tensor-site inclusions and their coefficient inclusion
in the crossed product are faithful. This can be seen directly
using faithful spatial representations for tensor products and
the regular covariant representation for the crossed product,
as detailed in the preceding
[alternating-conjugate audit](stw61-alternating-conjugate-shift-obstruction-2026-09-05.md).

The image of r is the two-site isometry

```text
R_01=(v_1 tensor v_1 + v_2 tensor v_2)/sqrt(2),
```

at sites zero and one. Its translate is the same expression at
sites one and two. Therefore the commutator norm is determined
inside the faithful three-site tensor product D tensor D tensor D.
Write

```text
R=(v_1 tensor v_1 tensor 1+v_2 tensor v_2 tensor 1)/sqrt(2),
S=(1 tensor v_1 tensor v_1+1 tensor v_2 tensor v_2)/sqrt(2),
P_R=RR*,   P_S=SS*.
```

Then R*R=S*S=1 and

```text
||Phi_D([z,q])|| = ||P_S-P_R||.
```

## 4. Exact overlap and the Cuntz norm

Using v_i*v_j=delta_ij, one obtains

```text
R*S=T/2,
T=v_1* tensor 1 tensor v_1 + v_2* tensor 1 tensor v_2.
```

Let P=v_1v_1*+v_2v_2*. Direct multiplication gives

```text
T*T=P tensor 1 tensor 1,
TT*=1 tensor 1 tensor P.
```

For D=O_2 we have P=1. Thus T is unitary and

```text
P_R P_S P_R = P_R/4,
P_S P_R P_S = P_S/4.
```

For any two projections E,F,

```text
||E-F||=max(||(1-F)E||,||(1-E)F||).
```

Applying this identity to the preceding overlap equations yields

```text
||P_S-P_R||=sqrt(1-1/4)=sqrt(3)/2.
```

This is an exact norm computation, not an estimate inferred from
a finite-dimensional compression. The tensor factors themselves
are properly infinite. The unitary producing this image is the
image of the explicitly constructed W from Section 2.

## 5. The Toeplitz defect restores norm one

For D=T_2, the projection P=1-e is proper. Thus T is a partial
isometry with a genuine defect, and

```text
R* P_S R=TT*/4=(1 tensor 1 tensor P)/4.
```

In particular,

```text
R*(1-P_S)R=1-(1 tensor 1 tensor P)/4
```

has norm one: on the nonzero projection 1 tensor 1 tensor e it
acts as the identity. Therefore ||(1-P_S)R||=1, and hence
||(1-P_S)P_R||=1. The projection-difference identity gives

```text
||P_S-P_R||=1.
```

Contractivity of Phi_T implies ||[z,q]||_C>=1. The general upper
bound for a unitary-projection commutator is one, giving equality.
There is also an independent check: q is full and supported in
the fixed proper Toeplitz projection s_1s_1*+s_2s_2*, so the
[fixed-corner obstruction](stw61-mixed-corner-rotation-obstruction-2026-09-05.md)
applies directly.

## 6. What this resolves and what it leaves open

The explicit formulas provide a test for proposed arguments using
the full properly infinite coefficient algebra. The O_2 shift
model admits a strict norm bound for this liftable mixed conjugate;
the T_2 shift model and the universal source do not. Consequently,
an estimate in the O_2 shift quotient cannot establish the strict
BRR bound in the source. Nor can a maximal-norm assertion for all
mixed conjugates be justified by that particular quotient test.

This does not contradict the earlier alternating-word theorem:
W=MFJ uses matrix sums and mixed isometry coefficients, and is not
asserted to have the alternating form covered there. It also does
not contradict the MF result: the full Toeplitz coefficient
algebra has no unital matrix-quotient representation.

The calculation produces no strict universal-source commutator
and no null-homotopy or surviving component for the LXI candidate.
It isolates one exact obstacle for a natural proper-infinite
test model and supplies explicit algebraic data against which
future constructions can be checked. LXI remains open.
