---
rg: 2
id: balanced-target-polar-and-quasiregular-hecke-absorber-proof
kind: proof
proves:
  - occurrence-conditioned-balanced-polar-discards-the-hall-excess
---

# Proof

## 1. The universal balanced-polar absorber

Let P,Q be projections in M_d(C), with
```text
tr_d(P)=p>=q=tr_d(Q).
```
Choose a subprojection P_0<=P of rank equal to rank(Q), and choose a
partial isometry V with
```text
V^*V=P_0,                  VV^*=Q.
```
There is a unitary U extending V and satisfying
```text
U(P-P_0)U^*<=1-Q.                                         (BHP1)
```
Indeed, extend an orthonormal-basis bijection from P_0H to QH first,
then one from (P-P_0)H into (1-Q)H; the remaining source and target
dimensions are equal, so complete it to a unitary.  Equation (BHP1)
gives
```text
QUP=UP_0=V.                                              (BHP2)
```
Thus V is exactly the polar of the occurrence-conditioned compression
QUP.  At the same time
```text
(1-Q)UP=U(P-P_0)
```
carries the entire excess rank p-q.  Target containment of the polar and
positive leakage of the original occurrence are perfectly compatible.

The same statement applies to a general operator A with initial support
P.  Let W be its polar and S=WW^*.  Choose S_0<=S of trace q and a
unitary G sending S_0 onto Q and S-S_0 into 1-Q.  Since A maps onto S,
the operator
```text
T=QGA=GS_0A
```
has full range Q.  Its polar has an initial projection P_0<=P of trace q,
while the complementary initial dimension p-q is discarded.  If
A^*A>=c^2P, then
```text
||(1-Q)GA||_2^2>=c^2(p-q).                               (BHP3)
```
So even a dimension-free leakage lower bound survives this construction;
it simply lives outside the balanced polar.

Conversely, for any T=QAP,
```text
V=polar(T),       P_0=V^*V,       Q_0=VV^*
```
satisfy
```text
P_0<=P,       Q_0<=Q,       tau(P_0)=tau(Q_0)<=tau(Q).    (BHP4)
```
If Q_0=Q, then tau(P_0)=q and the discarded initial trace is at least
p-q.  Thus forming the polar of a target compression can never preserve
a source support of larger trace.

There is also no automatic uniform extraction theorem.  Full row support
of T does not bound its least nonzero singular value.  The matrices
```text
diag(1,...,1,1/n)
```
have full support but no dimension-independent lower bound.  A polar
used in approximate representations requires a separate quantitative
spectral-gap certificate.

## 2. A balanced polar does not authenticate a smaller source algebra

Let D_1,...,D_r act on Q and let V be the balanced partial isometry above.
Defining
```text
C_j=V^*D_jV
```
makes
```text
D_jV=VC_j
```
whenever Q reduces D_j.  But this tautological source tuple is unitarily
equivalent to the target tuple on Q.  In particular it has the same
polynomial-identity degree.  A degree-two-to-degree-four contradiction
requires an independently occurrence-typed source tuple satisfying the
degree-two identity before V is chosen.

More generally, fixing only some covariance rows leaves a commutant
gauge on each common finite-head isotypic block.  Multiplying V on the
right by a unitary in that commutant preserves its support and all fixed
rows.  The remaining rows cannot be inferred from support, trace, or
from the word occurrence alone.  This is exactly why the two Q-labelled
rows of the balanced Jacobson center fold do not determine its two
T-labelled rows.

## 3. The GL finite-truncation Hecke face is in the trivial head type

Let K<F be finite groups and let
```text
pi=Ind_K^F(1) on l^2(F/K).
```
Write
```text
p_K=|K|^-1 sum_(k in K) pi(k),
p_F=|F|^-1 sum_(f in F) pi(f),
p=p_K-p_F.                                               (BHP5)
```
The F-fixed vectors are contained in the K-fixed vectors, so p is a
projection.  It is nonzero whenever K<F: the indicator of the base coset
is K-fixed and is not constant, and subtracting its constant component
gives a nonzero vector in p.

Every k in K acts as the identity on p.  Therefore, if C<=K and e_chi is
a nontrivial C-character projection,
```text
e_chi p=0.                                               (BHP6)
```
Likewise, for every involution z in K,
```text
(1-pi(z))p/2=0.                                          (BHP7)
```
The same calculation holds on the intertwiner space
Hom_K/Hom_F: the extra K-intertwiner is carried by the trivial K-type.

Apply this to
```text
F=GL_(28N)(F_2),             K=GL_28(F_2)
```
in the finite-truncation packet.  Every selected qutrit atom e_a has a
nontrivial order-three character, and every selected head carrier
E=(1-H)/2 is a negative involution cut.  Hence
```text
e_a p=0,                   E p=0.                         (BHP8)
```
In particular the three-line source G_(sigma,+)(e_0+e_1) and the target
Ee_b both annihilate the sole K-fixed/F-orthogonal Hecke mode.  A raw
transporter may move that mode into other K-double-coset sectors, but the
right source cut already removes it.  If a cut is applied only after the
transport, the result is an ordinary finite-dimensional Hecke operator
inside pi, and its missing mass is carried by the other finite cosets.

For reference, in the left regular representation of F the analogous
Reynolds difference has exact trace
```text
tau_F(p_K-p_F)=1/|K|-1/|F|.                              (BHP9)
```
In the quasiregular representation its normalized rank is
```text
(|K backslash F/K|-1)/[F:K].                             (BHP10)
```
Both formulas make the finite absorber explicit.

## 4. Application to the three-line target compression

Let
```text
A=g_2 X R,                 Q_b=Ee_b,
T_b=Q_b A.
```
The established source support P of A has trace
```text
p=5/72       or       1/16,
```
whereas tau(Q_b)=1/18.  If T_b has full range Q_b, its polar is indeed
an occurrence-conditioned partial isometry with source and range traces
exactly 1/18.  But (BHP4) then says that it has discarded exactly
```text
1/72       or       1/144                               (BHP11)
```
of initial support.  The quantitative outside-target leakage proved for
A is carried by that discarded part; it is not a defect of the balanced
polar.

If T_b does not have full range, the polar is smaller still.  Full range
alone would also not give a uniform polar modulus, and no established
row identifies its tautological source tuple with the independently
known degree-two Jacobson tuple.  The quasiregular calculation
(BHP8) shows that the remaining continuous finite-head Hecke mode cannot
supply that identification.

Therefore the equal-trace occurrence is a valid analytic partial
isometry but not a nonhyperlinearity witness.  To advance, one must use
an additional mixed S/T relation which simultaneously gives a lower
singular bound for T_b and intertwines the already named degree-two
source rows with the literal degree-four target rows.  Neither balanced
support nor the K-versus-F Hecke face provides those statements.
