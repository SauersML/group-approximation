---
rg: 2
id: tfd-tensorization-gaps-every-finite-deck-packet
kind: claim
title: Property TFD gives a uniform gap for every finite Schreier deck packet
artifacts:
  - research/frobenius-tensorization-of-schreier-returns-proof.md
distinct_from:
  index-three-frames-leave-deck-holonomy-uncontrolled: that exhibits a bad translated row in the natural infinite induced host; this proves that the complete averaged row packet is uniformly coercive in every finite-dimensional host.
  cayley-expansion-aligns-isometry-frame-coranges: that uses expansion of the finite quotient to align a field indexed by the quotient; this tensorizes a candidate representation with the quotient regular representation and applies the fixed ambient group's property TFD gap.
  exact-core-domain-does-not-descend-to-normal-quotient: that separates the vacuum row from one translated row without a finite-host energy estimate; this identifies the exact finite-host Laplacian and its kernel.
---

Let \(\Gamma=\langle S\rangle\) have property \((T;FD)\), with normalized
finite-dimensional Kazhdan gap \(\kappa>0\):
\[
 \frac1{|S|}\sum_{s\in S}\|\rho(s)\eta-\eta\|^2
 \geq \kappa\,\operatorname{dist}
       \bigl(\eta,\mathcal H^{\rho(\Gamma)}\bigr)^2       \tag{FDP1}
\]
for every finite-dimensional unitary representation \(\rho\).
Let \(\Lambda\triangleleft\Gamma\) have finite index, put
\(Q=\Gamma/\Lambda\), and choose an arbitrary section
\(\tau:Q\to\Gamma\), \(\tau(1)=1\).  Its Schreier returns are
\[
 r(s,q)=\tau(sq)^{-1}s\tau(q)\in\Lambda
 \qquad(s\in S,\ q\in Q).                                \tag{FDP2}
\]

For every finite-dimensional unitary representation
\(\pi:\Gamma\to U(\mathcal H)\), let \(P_\Lambda\) project onto
\(\mathcal H^{\pi(\Lambda)}\).  Then the complete return Laplacian obeys
the section- and index-independent operator inequality
\[
 \frac1{|S||Q|}\sum_{s,q}
  \bigl(\pi(r(s,q))-1\bigr)^*
  \bigl(\pi(r(s,q))-1\bigr)
 \ \geq\ \kappa(1-P_\Lambda).                            \tag{FDP3}
\]

Thus the averaged deck-holonomy seam has no finite-dimensional
countermodel.  If the common fixed space is zero, the normalized average
return energy of every isometry \(V:\mathbb C^d\to\mathcal H\) is at least
\(\kappa\).  More generally, if
\[
 D_{\rm ret}(V)^2
 =\frac1{|S||Q|d}\sum_{s,q}
   \|(\pi(r(s,q))-1)V\|_{\mathrm F}^2,                   \tag{FDP4}
\]
then a spectral cut gives a projection \(e\) on the source and a
\(\Gamma/\Lambda\)-representation corner on \(e\mathbb C^d\) with
\[
 \frac{\operatorname{rank}e}{d}
 \geq1-\frac{2D_{\rm ret}(V)^2}{\kappa},\qquad
 \frac1d\|W-Ve\|_{\mathrm F}^2
 \leq\frac{2D_{\rm ret}(V)^2}{\kappa}.                   \tag{FDP5}
\]
When \(V\) exactly intertwines a core \(B<\Gamma\), one may take
\(e\in\beta(B)'\) and \(W\) to be a relative quotient corner.

Apply this to
\[
 \Gamma=PSL_2(\mathbb Z[1/2]),\qquad
 \Lambda_N=\langle\!\langle t^N\rangle\!\rangle,\qquad
 Q=G_N.
\]
The property-\((T;FD)\) gap of the fixed arithmetic group makes
\(\kappa\) independent of \(N\), the section, the representation dimension,
and the size of the return packet.  Quotient property \((\tau)\) is not
needed.

The natural core induction
\(\operatorname{Ind}_B^\Gamma\beta\) remains outside this theorem because
its Stinespring space is infinite-dimensional.  Property \((T;FD)\) cannot
be applied there; doing so would incorrectly upgrade it to property
\((T)\).  Nor does (FDP3) prove that the three endpoint relator defects
produce a finite-dimensional \(\Gamma\)-host with small \(D_{\rm ret}\).
Constructing that host, or bounding its return energy directly by
\(E_{\rm end}\), is precisely the finite-corner/optimized-selector gate.
Therefore this closes the finite-host deck-gap subproblem but not (OPD11)
or the non-hyperlinearity root.

DERIVATION
frobenius-tensorization-of-schreier-returns-proof
