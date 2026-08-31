---
rg: 2
id: kt-congruence-stabilizer-traps-the-pointed-inverse-orbit-proof
kind: proof
title: Congruence stabilizers trap every bounded-depth Kun--Thom return packet
proves:
  - kt-first-laurent-defect-has-exponentially-thin-gamma-orbit
requires:
  - kt-truncated-cone-inverse-rank-and-pointed-wall-proof
  - intermediate-ring-truncations-preserve-the-kt-named-return-proof
---

# Congruence stabilizers trap every bounded-depth Kun--Thom return packet

## 1. Rings, cosets, and the positive-depth filtration

Work over `F_2`. Put

~~~text
S=F_2[x_1,y,x_3],
P=F_2[x_1,x_1y,x_3] subset S,
T_N=S/(x_1,y,x_3)^(N+1),
P_N=image(P->T_N),
Q_N=EL_3(T_N),
Gamma_N=EL_3(P_N),
Omega_N=Q_N/Gamma_N.
~~~

We use right cosets, with `Q_N` acting on the left. The monomial description

~~~text
P_N=span{x_1^a y^b x_3^c:a+b+c<=N and a>=b}              (1)
~~~

shows that `P_N` is a finite local ring: its positive-degree part is a
nilpotent maximal ideal and its residue field is `F_2`. Therefore

~~~text
SL_3(P_N)=EL_3(P_N)=Gamma_N,
SL_3(T_N)=EL_3(T_N)=Q_N.                                   (2)
~~~

For completeness, (2) is just elementary elimination over either local ring.
A unimodular column contains a unit. Elementary row operations move that
unit to the first position, clear the other entries, and induction clears
the remaining `2`-by-`2` block. In characteristic two no separate sign
matrix is needed.

For an integer `M>=1`, let

~~~text
I_(N,M)=x_1^M P_N,
C_(N,M)={gamma in Gamma_N:gamma=I mod I_(N,M)}.             (3)
~~~

This is a subgroup because `I_(N,M)` is an ideal of `P_N`. A basis of
`P_N/I_(N,M)` consists exactly of the monomials in (1) with

~~~text
0<=a-b<M.                                                   (4)
~~~

If

~~~text
f(t)=#{(b,c):2b+c<=t}=floor((t+2)^2/4),
~~~

then its dimension is exactly

~~~text
b_(N,M)=sum_(d=0)^(min(M-1,N)) floor((N-d+2)^2/4).          (5)
~~~

In particular,

~~~text
b_(N,M)<=M(N+2)^2/4.                                       (6)
~~~

Reduction of matrix entries modulo `I_(N,M)` gives a sharper local-group
index estimate

~~~text
[Gamma_N:C_(N,M)]<=2^(8b_(N,M)).                           (7)
~~~

Here is the complete count. Put `R=P_N/I_(N,M)` and
`b=b_(N,M)`. This is a local ring with residue field `F_2` and maximal
ideal of size `2^(b-1)`. Reduction to the residue field has kernel
`I+M_3(maximal ideal)`, so

~~~text
|GL_3(R)|=|GL_3(F_2)| 2^(9(b-1)).
~~~

The determinant map onto `R^times` is surjective and
`|R^times|=2^(b-1)`. Therefore

~~~text
|SL_3(R)|=168*2^(8(b-1)) < 2^(8b).
~~~

The reduction image of `Gamma_N` lies in this special linear group and
its kernel is `C_(N,M)`, proving (7). No generation or bounded-width
assertion is hidden in the estimate.

## 2. The first Laurent site has a codimension-two stabilizer

Let

~~~text
h_N=e_12(y)=I+yE_12 in Q_N.
~~~

Since the characteristic is two and `E_12^2=0`, `h_N^(-1)=h_N`.
Take `gamma in C_(N,2)` and write

~~~text
gamma=I+x_1^2 A,              A in M_3(P_N).
~~~

Direct multiplication gives

~~~text
h_N^(-1) gamma h_N
 =I+x_1^2(A+yE_12 A+yA E_12+y^2 E_12 A E_12).             (8)
~~~

Every entry added in (8) lies in `P_N`. Indeed the only new scalar
multipliers are

~~~text
x_1^2,        x_1^2 y=x_1x_2,        x_1^2 y^2=x_2^2,     (9)
~~~

and all three belong to `P`. The matrix in (8) has determinant one, so
(2) puts it in `Gamma_N`. Equivalently,

~~~text
C_(N,2) subset Stab_(Gamma_N)(h_N Gamma_N).                (10)
~~~

Let

~~~text
O_N=Gamma_N h_N Gamma_N/Gamma_N.
~~~

Orbit--stabilizer, (7), and (10) imply

~~~text
|O_N|<=[Gamma_N:C_(N,2)]<=2^(8b_(N,2)).                    (11)
~~~

Formula (5) gives the closed forms

~~~text
b_(2m,2)=(m+1)(2m+1),
b_(2m+1,2)=(m+1)(2m+3).                                   (12)
~~~

These are the quantities denoted `b_N` in the claim.

## 3. The ambient coset set has cubic exponential size

Write `V_N=T_N/P_N` as an additive vector space. The map

~~~text
V_N -> Omega_N,       f+P_N |-> e_12(f)Gamma_N             (13)
~~~

is injective. If two cosets in (13) agree, then
`e_12(f-f') in Gamma_N`. Every entry of a matrix in
`Gamma_N=EL_3(P_N)` lies in `P_N`, so `f-f' in P_N`.

The complementary monomial basis of `V_N` consists of the triples
`a+b+c<=N` with `a<b`. Its dimension, computed by pairing `a<b`
with `a>b`, is

~~~text
v_(2m)=m(m+1)(4m+5)/6,
v_(2m+1)=(m+1)(m+2)(4m+3)/6.                              (14)
~~~

Let `t_N=dim_F2(T_N)` and `p_N=dim_F2(P_N)`. The monomial
basis above gives `t_N-p_N=v_N`. Applying the exact local-ring count from
Step 1 to both rings yields

~~~text
|Q_N|=168*2^(8(t_N-1)),
|Gamma_N|=168*2^(8(p_N-1)).
~~~

Therefore the ambient coset cardinality is not merely bounded below by the
injection (13); it is exactly

~~~text
|Omega_N|=[Q_N:Gamma_N]=2^(8v_N).                          (15)
~~~

Combining (11) and (15),

~~~text
|O_N|/|Omega_N|<=2^(8(b_(N,2)-v_N))
                  =2^(-2N^3/3+O(N^2))->0.                 (16)
~~~

This proves the advertised thinness of the full `Gamma_N`-orbit, not
merely of an orbit under a chosen Kazhdan generating set.

## 4. Every bounded Laurent-depth packet is equally thin

For a monomial `x_1^a y^b x_3^c`, define its positive-core deficit by

~~~text
def(x_1^a y^b x_3^c)=max(b-a,0).                           (17)
~~~

For a polynomial, take the maximum deficit of its monomials. The deficit
is subadditive under multiplication.

Let `F` be a finite subset of `EL_3(S)`. Choose `M_F` at least the
maximum, over every entry `u` of `g`, every entry `v` of `g^(-1)`,
and every `g in F`, of

~~~text
def(u)+def(v).                                             (18)
~~~

If `gamma=I+x_1^(M_F)A in C_(N,M_F)`, then

~~~text
g^(-1) gamma g=I+x_1^(M_F)g^(-1)Ag.                       (19)
~~~

Every entry after the identity in (19) is a sum of terms
`x_1^(M_F)uav`, where `a in P_N`. Equations (17)--(18) show that every
such term lies in `P_N`. The matrix has determinant one, so (2) gives

~~~text
g^(-1) C_(N,M_F) g subset Gamma_N.                         (20)
~~~

Thus `C_(N,M_F)` fixes `gGamma_N`. From (7),

~~~text
|Gamma_N g Gamma_N/Gamma_N|
 <=2^(8b_(N,M_F)),                                        (21)
~~~

and hence

~~~text
| union_(g in F) Gamma_N gGamma_N |
 <=|F| 2^(8b_(N,M_F))
 <=|F| 2^(2M_F(N+2)^2).                               (22)
~~~

For fixed `F`, (22) is `2^(O_F(N^2))`, whereas (15) is
`2^(2N^3/3+O(N^2))`.

The same calculation gives a useful moving-window version. For packets
`F_N`, let `M_N` satisfy (18). If

~~~text
M_N=o(N),             log_2 |F_N|=o(N^3),                 (23)
~~~

then

~~~text
| union_(g in F_N) Gamma_N gGamma_N |/|Omega_N| ->0.       (24)
~~~

The exact ambient cardinality makes the linear-depth conclusion much
stronger. If `M_N=floor(cN)+O(1)` with a fixed `0<=c<1`, then (5) gives

~~~text
b_(N,M_N)
 =N^3(1-(1-c)^3)/12+O(N^2).                               (LW1)
~~~

Consequently, when `log_2|F_N|=o(N^3)`, the base-two logarithmic density
of the complete saturation is at most

~~~text
-(2/3)(1-c)^3 N^3+o(N^3),                                 (LW2)
~~~

and tends to minus infinity. Thus every fixed fractional depth `cN`,
not just a small initial fraction, remains trapped.

There is also an exact near-boundary formula. Put `L=N-M`, with
`1<=M<=N`, and retain `f(t)=floor((t+2)^2/4)`. Swapping the exponents
`a,b` shows

~~~text
v_N-b_(N,M)=sum_(t=0)^L f(t)-f(N).                        (LW3)
~~~

The first term counts positive-difference monomials of difference at least
`M`; the subtracted `f(N)` is the diagonal `a=b`. Hence

~~~text
v_N-b_(N,M)=L^3/12-N^2/4+O(L^2+N).                        (LW4)
~~~

In particular, if `L/N^(2/3)->infinity` and
`log_2|F_N|=o(L^3)`, the saturation is thin. At the critical scale
`L=C N^(2/3)`, it is thin for

~~~text
C>3^(1/3)
~~~

provided `log_2|F_N|=o(N^2)`.

Therefore a packet-density proof with subcubic packet size must drive its
denominator depth all the way to `N-o(N)`. For ordinary word balls, the
congruence firewall persists at least through depth
`N-(3^(1/3)+epsilon)N^(2/3)`. The only window not excluded by this
mechanism is the near-full truncation boundary.

## 5. Exact regular-character Clifford reservoir

Put `M_N=|Omega_N|` in this section only and define

~~~text
H_N=ell^2(Q_N) tensor (C^2)^(tensor Omega_N),
D_N=dim(H_N)=|Q_N| 2^(M_N).                               (25)
~~~

Let `Q_N` act by the tensor product of its left regular action on
`ell^2(Q_N)` and its permutation action on the qubit factors. Let the
lamp at `z in Omega_N` act by Pauli `Z_z`. This is a representation
`rho_N` of

~~~text
W_N=(direct_sum_(Omega_N) C_2) rtimes Q_N.                 (26)
~~~

Its normalized character is exactly the regular character. If the actor
component `q` is nonidentity, the left-regular factor has trace zero. If
`q=1` but the lamp `f` is nonzero, the tensor product contains a
nontrivial Pauli `Z` and again has trace zero. Since
`dim H_N=|W_N|`, the representation is in fact unitarily equivalent to
the left regular representation.

Let `o_N=Gamma_N`, and set

~~~text
p_N=(I+Z_(o_N))/2,       U_(h,N)=rho_N(h_N).               (27)
~~~

The group `Gamma_N` fixes `o_N`, so `p_N` commutes with its entire
image. The point `h_No_N` differs from `o_N`, and the two coordinate
projections have product trace `1/4`. Hence

~~~text
||[p_N,U_(h,N)]||_2
 =||p_N-U_(h,N)p_NU_(h,N)^*||_2
 =1/sqrt(2).                                               (28)
~~~

Thus the distinguished wall has positive normalized Hilbert--Schmidt mass
even though its complete `Gamma_N`-orbit occupies vanishing site density.

Here is the exact adjoint-rank audit. Let

~~~text
E_N={o_N} union O_N.
~~~

The algebra of all lamp operators supported on `E_N` is
`M_(2^|E_N|) tensor I`. It is invariant under conjugation by
`Gamma_N`. Even granting the entire actor matrix algebra on
`ell^2(Q_N)`, the containing subspace

~~~text
M_(|Q_N|) tensor M_(2^|E_N|) tensor I_(2^(M_N-|E_N|))
~~~

has dimension `|Q_N|^2 4^|E_N|`, while
`End(H_N)` has dimension `|Q_N|^2 4^M_N`.
Its normalized adjoint-rank fraction is therefore exactly

~~~text
4^(|E_N|-M_N)<=4^(1+|O_N|-|Omega_N|)->0.                  (29)
~~~

Every Pauli word, every Clifford circuit supported on these sites, and
every Reynolds average under the full finite image `Gamma_N` remains in
this subspace. Replacing `{1,h}` by a fixed packet `F` and using its
`Gamma_N`-saturation gives the same conclusion by (22).

## 6. Canonical moments and the precise firewall

Let

~~~text
H=EL_3(F_2[x_1,y,x_3]),          Gamma=EL_3(P).
~~~

The three elements `x_1,x_1y,x_3` are algebraically independent, so
`P` is a polynomial ring over `F_2`. Suslin elementary generation gives

~~~text
SL_3(P)=EL_3(P)=Gamma.                                    (30)
~~~

This verifies the separation assertion rather than assuming it. Suppose
`gGamma` and `g'Gamma` are distinct cosets in `H/Gamma`. Then
`d=g'^(-1)g` is not in `Gamma`. If every entry of `d` belonged to
`P`, equation (30) would put `d` in `Gamma`, a contradiction.
Thus one entry contains a monomial `x_1^a y^b x_3^c` with `a<b`.
For every truncation deeper than the degree of that entry, the same
monomial shows that the image of `d` is not in `Gamma_N`. Hence every
fixed finite coset table in `H/Gamma` injects into `Omega_N` for all
large `N`.

The maps `H->Q_N` and `Gamma->Gamma_N` are onto because elementary
root entries lift. They induce quotient maps from the coherent
intermediate wreath product

~~~text
W_H=(direct_sum_(H/Gamma) C_2) rtimes H
~~~

onto `W_N`: lamps in one finite-quotient fiber are added modulo two.
The eventual injectivity of each fixed coset table prevents cancellation
of any fixed nonzero lamp. Polynomial truncation also separates each fixed
nonidentity actor. Therefore these quotient maps separate every fixed
element of `W_H`.

Pulling `rho_N` back along these maps yields normalized characters
converging pointwise to the canonical character of `W_H`.
Equations (28)--(29) occur inside exact regular-character models; they are
not caused by trace pollution.

We have therefore exhausted the proposed finite-packet amplification.
The complete finite `Gamma_N` image, not merely a Kazhdan subset, sees
only an exponentially thin saturation of the first Laurent site. Adding a
finite Clifford packet does not change its support, and granting arbitrary
multiplicity on the complementary qubits leaves (28) untouched.

This is a firewall, not a nonhyperlinearity proof. Relations from the full
Laurent actor can move through denominator depth comparable to `N`;
they are absent from the intermediate actor used here. A positive
Kun--Thom argument must control such a linear-depth moving window. A
countermodel must extend these exact intermediate models across that same
window. Neither extension is proved here, so the global root remains open.
