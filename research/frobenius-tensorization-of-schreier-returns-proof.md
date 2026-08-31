---
rg: 2
id: frobenius-tensorization-of-schreier-returns-proof
kind: route
title: Tensor the candidate with the quotient regular representation
target: tfd-tensorization-gaps-every-finite-deck-packet
requires:
  - tfd-finite-corner-collapse-and-rfd-firewall
  - index-three-frames-leave-deck-holonomy-uncontrolled
---

# One orbit isometry contains every return row

Let \(\lambda_Q\) be the left regular representation of \(Q\), with
\(\lambda_Q(s)\delta_q=\delta_{sq}\).  On
\(\mathcal H\otimes\ell^2(Q)\) put
\[
 \rho(s)=\pi(s)\otimes\lambda_Q(s).
\]
This is finite-dimensional whenever \(\pi\) is.  Define
\[
 J\xi=\frac1{\sqrt{|Q|}}\sum_{q\in Q}
       \pi(\tau(q))\xi\otimes\delta_q.                    \tag{1}
\]
Every summand has norm \(\|\xi\|\), so \(J\) is an isometry.

The coefficient of \(\rho(s)J\xi\) at \(\delta_{sq}\) is
\(\pi(s\tau(q))\xi\), whereas the corresponding coefficient of \(J\xi\)
is \(\pi(\tau(sq))\xi\).  By (FDP2),
\[
 \pi(s\tau(q))
 =\pi(\tau(sq))\pi(r(s,q)).
\]
Orthogonality of the quotient coordinates therefore gives the exact
identity
\[
 \|(\rho(s)-1)J\xi\|^2
 =\frac1{|Q|}\sum_{q\in Q}
   \|(\pi(r(s,q))-1)\xi\|^2.                             \tag{2}
\]
There is no word-length, section-length, or triangle-filling loss in (2).

# Finite Frobenius reciprocity identifies the kernel

Write a vector in the tensor product as
\(\zeta=\sum_q\zeta_q\otimes\delta_q\).  It is
\(\rho(\Gamma)\)-invariant exactly when
\[
 \zeta_{sq}=\pi(s)\zeta_q
 \qquad(s\in S,\ q\in Q).                                \tag{3}
\]
Equation (3) gives
\[
 \zeta_q=\pi(\tau(q))\zeta_1.
\]
Consistency at the identity coset says
\(\pi(\lambda)\zeta_1=\zeta_1\) for every
\(\lambda\in\Lambda\).  Conversely that condition makes the displayed
field invariant.  Hence
\[
 \bigl(\mathcal H\otimes\ell^2(Q)\bigr)^{\rho(\Gamma)}
 =J\bigl(\mathcal H^{\pi(\Lambda)}\bigr).                \tag{4}
\]
Since \(J\) is an isometry,
\[
 \operatorname{dist}\bigl(J\xi,
  (\mathcal H\otimes\ell^2(Q))^{\rho(\Gamma)}\bigr)
 =\|(1-P_\Lambda)\xi\|.                                  \tag{5}
\]

Apply (FDP1) to the finite-dimensional representation \(\rho\), substitute
(2) and (5), and average over \(s\).  For every \(\xi\),
\[
 \frac1{|S||Q|}\sum_{s,q}
 \|(\pi(r(s,q))-1)\xi\|^2
 \geq\kappa\|(1-P_\Lambda)\xi\|^2.
\]
Polarization of the two positive quadratic forms proves (FDP3).

# The return gap cuts out a quotient corner

The subspace \(\mathcal K=\mathcal H^{\pi(\Lambda)}\) reduces
\(\pi(\Gamma)\), because \(\Lambda\) is normal.  Let \(P_\Lambda\) be its
projection.  Taking the normalized trace of (FDP3) after compression by
\(V\) gives
\[
 \frac1d\operatorname{Tr}
 \bigl(V^*(1-P_\Lambda)V\bigr)
 \leq\frac{D_{\rm ret}(V)^2}{\kappa}.                    \tag{6}
\]
Put \(a=V^*P_\Lambda V\) and
\(e=1_{[1/2,1]}(a)\).  Then
\[
 \operatorname{rank}(1-e)
 \leq2\operatorname{Tr}(1-a)
 \leq\frac{2D_{\rm ret}(V)^2}{\kappa}d.                  \tag{7}
\]
Define
\[
 W=P_\Lambda Ve(eae)^{-1/2}.                             \tag{8}
\]
It is an isometry on \(e\mathbb C^d\) with range in \(\mathcal K\), and
\[
 W^*Ve=(eae)^{1/2}.
\]
Since \(1-\sqrt{x}\leq1-x\) on \([0,1]\),
\[
 \|W-Ve\|_{\mathrm F}^2
 \leq2\operatorname{Tr}(e(1-a))
 \leq\frac{2D_{\rm ret}(V)^2}{\kappa}d.                  \tag{9}
\]
Equations (7)--(9) prove (FDP5).

If \(\pi(b)V=V\beta(b)\) for \(b\in B\), then normality makes
\(P_\Lambda\) commute with \(\pi(B)\), so
\(a,e\in\beta(B)'\), and (8) intertwines the compressed core.  The action
of \(\pi(\Gamma)\) on \(\mathcal K\) kills \(\Lambda\), hence factors through
\(\Gamma/\Lambda\).  This is the stated relative quotient corner.

# Why the packed-lamp warning does not contradict the identity

A family
\((C_2)^{Q_n}\rtimes Q_n\) can have expanding quotients \(Q_n\) while its
averaged lamp-reflection Laplacian has gap \(4/|Q_n|\).  The ambient wreath
groups vary and have no uniform property-\((T;FD)\) constant.  Expansion of
the quotient alone cannot replace (FDP1).  For the Iwahori lane the ambient
group is fixed and has property \((T;FD)\), so the tensor representation
above supplies exactly the missing comparison in every finite-dimensional
host.

The remaining infinite-host boundary is real.  If the same argument worked
for arbitrary \(\pi\), (FDP3) for all finite-index kernels would be a
property-\((T)\)-type gap.  The arithmetic group is known not to have
property \((T)\).  Thus finite-dimensionality is the load-bearing
hypothesis, not a removable technicality.
