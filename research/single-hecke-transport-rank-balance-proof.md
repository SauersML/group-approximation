---
rg: 2
id: single-hecke-transport-rank-balance-proof
kind: route
title: Compute off-corner mass and the exact finite D8-in-S4 Hecke absorber
target: single-hecke-transport-cannot-carry-complete-context
requires: []
---

# Proof

## 1. Universal compression identities

Let (M,tau) be a finite von Neumann algebra with faithful normalized trace,
let Q be a projection, and let U be a unitary.  Put
```text
X=Q U Q,               R=U Q U^*.
```
Then
```text
Q-X X^* = Q U(1-Q)U^* Q,
Q-X^* X = Q U^*(1-Q)U Q.                                (SHT1)
```
Both right sides are positive.  Traciality gives the exact rank balance
```text
||(1-Q)U^*Q||_2^2
 =||Q U(1-Q)||_2^2
 =tau(Q)-tau(QR).                                        (SHT2)
```
Equivalently, the two off-diagonal blocks of a finite unitary carry the
same Hilbert--Schmidt mass.

More generally, if P_1,...,P_m are orthogonal projections summing to Q,
define the compressed transported effects
```text
R_v=Q U P_v U^* Q.
```
They are positive contractions and
```text
sum_v R_v=Q U Q U^*Q,
Q-sum_v R_v=Q U(1-Q)U^*Q.                               (SHT3)
```
Consequently they sum to Q if and only if the last positive operator
vanishes.  This says (1-Q)U^*Q=0, hence U^*QH is contained in QH.
The two projections Q and UQU^* have equal finite trace, so the inclusion
is equality.  Therefore
```text
sum_v R_v=Q    if and only if    UQU^*=Q.                 (SHT4)
```
The converse is immediate.  Thus plain compression through one
nonreducing stable letter can never transport a complete context.

For arbitrary unitaries G,H, compressed multiplication has the exact
defect
```text
(QGQ)(QHQ)-QGHQ=-QG(1-Q)HQ.                              (SHT5)
```
In particular
```text
||(QGQ)(QHQ)-QGHQ||_2
 <=min(||QG(1-Q)||_2,||(1-Q)HQ||_2).                     (SHT6)
```
No algebraic relation among the compressed words controls this defect
unless it also controls an off-corner block.

## 2. Canonical trace formula for a finite anchor

Let E be finite, let rho be an irreducible representation of degree d
and character chi, and let
```text
q_rho=(d/|E|) sum_(x in E) chi(x^-1)x
```
be its central idempotent.  In a group Gamma containing E, use the
canonical group trace tau.  For a stable letter t, set
```text
H=E intersect t^-1 E t.
```
Expanding coefficients at the identity gives
```text
||q_rho t q_rho||_2^2
 =tau(q_rho t^-1 q_rho t)
 =(d/|E|)^2 sum_(h in H)
      chi(h^-1) chi(t h t^-1).                           (SHT7)
```
Only h for which t h t^-1 lies in E occur.

If A<=E is abelian and eta is a character of A, put
```text
p_eta=|A|^-1 sum_(a in A) conjugate(eta(a))a.
```
The same coefficient calculation gives
```text
tau(q_rho t p_eta t^-1 q_rho)
 =d/(|E||A|) sum_(a in A: t a t^-1 in E)
      chi(t a t^-1) conjugate(eta(a)).                   (SHT8)
```

For an extraspecial group E of order 2d^2, the unique spin character is
d at 1, -d at the central involution J, and zero elsewhere.  Its
idempotent is simply
```text
q=(1-J)/2,                 tau(q)=1/2.                   (SHT9)
```
If t is free from E, the intersection in (SHT7) is trivial and
```text
||q t q||_2^2=1/4,
||(1-q)tq||_2^2=1/4.                                    (SHT10)
```
If t commutes with J, then q commutes with t and the leakage is zero.
Thus a nonreducing spin idempotent necessarily gives up global centrality
of its marking involution.

## 3. The smallest exact Hecke filter and its finite absorber

Take the dihedral subgroup of S_4
```text
E=<r=(1 2 3 4), s=(1 3)> isomorphic to D_8.
```
Its central involution and a noncentral commuting involution are
```text
J=r^2=(1 3)(2 4),
a=rs=(1 4)(2 3).
```
Let t=(3 4).  Then
```text
t a t^-1=J,             t J t^-1=a.                      (SHT11)
```
For the two-dimensional spin block put
```text
q=(1-J)/2,
p_epsilon=q(1+epsilon a)/2,        epsilon in {+1,-1}.
```
The two p_epsilon are orthogonal and sum to q.  Conjugating (SHT11)
gives
```text
q t p_+ t^-1 q=0,
q t p_- t^-1 q=p_-,
q t q t^-1 q=p_-.                                      (SHT12)
```
Under the canonical trace,
```text
tau(q)=1/2,       tau(p_+)=tau(p_-)=1/4.                 (SHT13)
```
So the nonnormal Hecke move implements one exact losing-pair zero, but
it deletes precisely half of the corner.  The missing positive effect is
p_+, and adjoining it restores a complete finite PVM.  All of this is
already realized by the 24-dimensional left regular representation of
S_4.  It is therefore a finite absorber, not a finite-versus-infinite
separation.

The same relations define the universal HNN extension
```text
Gamma_0=<E,t | t a t^-1=J>.
```
It is the fundamental group of a finite graph of finite groups, hence is
virtually free and residually finite.  Given any finite set F in Gamma_0,
residual finiteness supplies a finite quotient injective on F^-1 F.
The left regular representation of that quotient has exactly the same
canonical traces and normalized Hilbert--Schmidt inner products on the
span of F as the regular representation of Gamma_0.  In particular every
fixed finite collection of expressions built from q, t, and the
p_epsilon has an exact finite regular absorber.

More generally, any construction made only from finitely many finite
anchors and stable letters identifying finite subgroups is a finite graph
of finite groups and is virtually free.  Its maximal group C*-algebra is
RFD: pass to a finite-index free normal subgroup, use Choi RFD for the
free-group algebra, and embed the finite crossed product into a matrix
algebra over it.  Hence a fixed algebraic leakage or source-visible
element killed by every finite-dimensional representation is already
zero in the full group C*-algebra and cannot be revived by an infinite
tracial representation.

This proves both boundaries: a single nonreducing compression cannot
carry a unital context in any finite tracial completion, and the minimal
finite-subgroup Hecke relations have exact finite absorbers.
