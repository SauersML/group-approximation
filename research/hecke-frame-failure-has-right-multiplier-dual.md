---
rg: 2
id: hecke-frame-failure-has-right-multiplier-dual
kind: claim
title: Failure of a Hecke frame has a right-multiplier dual certificate
distinct_from:
  hecke-top-spectrum-coverage-controls-window: that gives the positive spectral-frame criterion; this gives the exact finite-dimensional alternative when the frame does not exist.
  regular-core-window-is-a-hecke-kraus-hull: that gives a numerical separator for the marked coefficient itself; this separates failure of the near-top subspace to cover the unit.
  congruence-endpoint-orbits-are-restriction-ring-fibers: that uses scalar multiplicity data for exact endpoints; this dual witness is a generally noncentral operator in the finite core commutant.
---

Let \(D\) be a finite-dimensional tracial \(C^*\)-algebra and let
\({\cal H}\subseteq L^2(D)\) be a complex linear subspace.  Define the
closed convex cone

\[
{\cal C}_{\cal H}
 =\left\{\sum_{j=1}^m A_j^*A_j:
          m<\infty,\ A_j\in{\cal H}\right\}\subseteq D_+.             \tag{HFD1}
\]

Exactly one of the following holds.

1. **Frame:** \(1\in{\cal C}_{\cal H}\).
2. **Dual obstruction:** there is \(Z=Z^*\in D\) such that

   \[
   \tau(Z)>0,\qquad
   P_{\cal H}R_ZP_{\cal H}\preceq0,                    \tag{HFD2}
   \]

   where \(R_Z(A)=AZ\) on \(L^2(D)\).

Indeed,

\[
\langle A,R_ZA\rangle_{L^2(D)}
 =\tau(A^*AZ)=\tau(ZA^*A).                             \tag{HFD3}
\]

Thus (HFD2) is precisely

\[
\tau(ZC)\leq0\quad(C\in{\cal C}_{\cal H}),\qquad
\tau(Z1)>0,                                             \tag{HFD4}
\]

which is incompatible with a frame.

The cone in (HFD1) is closed.  Its slice by \(\tau(C)=1\) is the convex
hull of the compact set

\[
\{A^*A:A\in{\cal H},\ \|A\|_2=1\},
\]

and trace controls the radial coordinate.  Hence if \(1\) is not in the
cone, finite-dimensional strong separation gives (HFD4), and every real
functional on \(D_{\rm sa}\) has the form \(C\mapsto\tau(ZC)\).  This proves
the alternative.

Apply the theorem to the near-top Hecke subspace

\[
{\cal H}_{N,\epsilon}
 =1_{[1-\epsilon,1]}(T_{X_N})L^2(D_N).                 \tag{HFD5}
\]

If the frame branch holds, then
'hecke-top-spectrum-coverage-controls-window' gives

\[
\Delta^{\rm reg}_{N,\beta_N}(X_N)\leq\sqrt{2\epsilon}.
\]

If it fails, (HFD2) gives a finite matrix certificate \(Z_{N,\epsilon}\).
At the exact top eigenspace, failure of full right support has the especially
simple witness: if \(p\) is the complementary right-support projection,
then \(Z=p\), \(\tau(p)>0\), and \(Ap=0\) for every top eigenvector \(A\).

Consequently a negative regular-Iwahori sequence must do more than make the
top eigenvalue equal or tend to one.  For every vanishing spectral window
capable of producing a small corner, it must retain a positive-trace
right-multiplier separator as in (HFD2).  Conversely, ruling out all such
separators proves spectral coverage and the finite corner.  No arithmetic
argument currently decides this alternative uniformly in the moving
congruence level; the root remains open.

DERIVATION
hecke-frame-failure-dual-proof
