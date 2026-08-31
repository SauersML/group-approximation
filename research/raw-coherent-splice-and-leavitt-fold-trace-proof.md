---
rg: 2
id: raw-coherent-splice-and-leavitt-fold-trace-proof
kind: proof
proves:
  - one-sided-raw-coherent-splices-are-absorbed-and-leavitt-fold-cannot-compress-fourier-mass
---

# Proof

## 1. Finite linear combinations in a residually finite group

Let Gamma be residually finite and let
```text
A_j=sum_(g in F_j) c_(j,g) g in C[Gamma],       1<=j<=m,
```
where every F_j is finite.  Fix a degree N.  Only finitely many group
elements occur in all star monomials of degree at most N in the A_j.
Let D be the finite set of the nonidentity elements among them.
Residual finiteness gives, for each d in D, a finite quotient which does
not kill d.  The product of these quotients gives one finite quotient
```text
phi_N:Gamma -> K_N
```
which kills none of D.

Let lambda_N be the left regular representation of K_N.  Its normalized
trace is the identity coefficient.  Hence, for every star polynomial P
of degree at most N,
```text
tr_(K_N)(P(lambda_N(phi_N(A_1)),...,lambda_N(phi_N(A_m))))
 =tau_Gamma(P(A_1,...,A_m)).                             (RCS1)
```
This is exact, not asymptotic.  In particular every finite packet of
Hilbert--Schmidt norms and inner products of fixed linear combinations
has a finite regular model.  Taking N to infinity gives a canonical
microstate sequence.

Apply this to the established one-sided Leavitt envelopes
```text
Lambda_T=<finite qutrit head,g_2,H,A,W,x_(ij)(T)>
          <=GL_28(B_-),        B_-=F_2<q,T>,

Lambda_S=<finite qutrit head,g_2,H,A,W,x_(ij)(S)>
          <=GL_28(B_+),        B_+=F_2<S,q,qT>.
```
Both groups are residually finite.  Therefore an amplitude of the form
```text
A_0+sum_j alpha_j a_j U b_j,                              (RCS2)
```
with a_j,b_j and A_0 in the finite head packet and with U using only the
raw T orientation, or only the raw S orientation, has all of its finite
trace moments absorbed by finite quotient regular representations.
Arbitrary word length and arbitrary complex coefficients in (RCS2) do
not change this conclusion.

## 2. The quantitative range loss of the three-line raw selector

Use the established three-line two-sided selector
```text
X=X_0+(1/4)X_1+(1/16)X_2.
```
On G=G_(sigma,+) it satisfies
```text
X^*X >=(1/256)G.                                         (RCS3)
```
The projections G and R lie in one fixed finite-head C*-algebra.  Put
```text
P=supp(RGR)
```
and let gamma be the least positive eigenvalue of RGR across that finite
C*-algebra.  Thus gamma>0 is dimension-independent and
```text
RGR>=gamma P.
```
Compressing (RCS3) gives
```text
(XR)^*(XR)=R X^*X R
 >=(1/256)RGR
 >=(gamma/256)P.                                         (RCS4)
```
In particular XR has initial support P.  The two possible source traces
and the target trace are
```text
tau(P)=5/72     or     1/16,
tau(Q_b)=tau(Ee_b)=1/18.                                 (RCS5)
```

We use a general finite-trace estimate.  If A^*A>=c^2P, with P the
initial support of A, then AA^*>=c^2R_A on its range projection R_A.
For every projection Q,
```text
||(1-Q)A||_2^2
 =tau(AA^*(1-Q))
 >=c^2 tau(R_A(1-Q))
 >=c^2(tau(P)-tau(Q)).                                   (RCS6)
```
The last inequality uses tau(R_A)=tau(P) and
tau(R_AQ)<=tau(Q).

Taking A=g_2XR, c^2=gamma/256, and Q=Q_b gives
```text
||(1-Q_b)g_2XR||_2^2 >=gamma/18432       if sigma=+,
||(1-Q_b)g_2XR||_2^2 >=gamma/36864       if sigma=-.      (RCS7)
```
Thus the missing range is not merely nonzero: it has a dimension-free
energy floor in every tracial representation retaining the stated
source and target traces.

Let B be any finite-head coherent correction.  If it cancels the
outside-target component,
```text
(1-Q_b)(g_2XR+B)P=0,
```
then (RCS7) forces
```text
||BP||_2^2 >=gamma/18432       or       gamma/36864.      (RCS8)
```
More decisively, if (g_2XR+B)P were still bounded below on all of P and
had range in Q_b, its initial and range supports would have equal trace,
forcing tau(P)<=tau(Q_b), contrary to (RCS5).  Therefore a correction can
cancel the leaked amplitude only by creating a kernel of trace at least
```text
tau(P)-tau(Q_b)=1/72       or       1/144.                (RCS9)
```
This statement holds in every finite von Neumann algebra, not only in
matrix algebras.

## 3. Why the literal Leavitt fold does not occurrence-type Fourier mass

In L=L_(F_2)(1,2), the matrix
```text
F=[[0,0,t_0],
   [0,0,t_1],
   [s_0,s_1,0]]
```
satisfies
```text
F^2=I,
F R_coord=Q_coord F,                                    (RCS10)

R_coord=diag(1,1,0),       Q_coord=diag(0,0,1).
```
Indeed t_i s_j=delta_(ij) gives the upper 2-by-2 identity block and
s_0t_0+s_1t_1=1 gives the last diagonal entry.  After stabilization this
invertible matrix lies in the elementary Leavitt group.

Equation (RCS10) is a ring-module equivalence between singular coordinate
idempotents.  It is not a relation between group-algebra Fourier
projections in an arbitrary unitary representation.  This distinction is
forced by trace.  If f is a unitary group element and P,Q are projections
with
```text
fP=Qf,
```
then fPf^*=Q, so every tracial representation has
```text
tau(P)=tau(Q).                                           (RCS11)
```
Even the weaker range condition QfP=fP implies
fPf^*<=Q and hence tau(P)<=tau(Q).

For the qutrit Fourier cuts in question,
```text
P=e_0+e_1,            Q=e_b,
tau(P)=2/9,           tau(Q)=1/9.                        (RCS12)
```
Thus no unitary group occurrence of F can satisfy the desired two-to-one
Fourier transport or even range containment.  Whitehead factorization of
diag(F,F) into elementary group generators does not alter this: it
factorizes an invertible ring matrix, but it does not turn R_coord and
Q_coord into intrinsic group-algebra projections.  Any finite-head
attempt to name those coordinate cuts must introduce hidden character
sectors or leakage so that (RCS11) remains valid.

Combining the three sections proves the boundary.  One raw orientation
plus finite coherent coefficients is residually finite and has exact
finite absorbers.  Both orientations can make the three-line source
bounded below, but every target-contained correction must delete the
Hall excess.  The Leavitt non-IBN fold cannot bypass that deletion after
the source and target are occurrence-typed by finite-subgroup Fourier
projections.
