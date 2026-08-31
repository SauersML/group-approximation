---
rg: 2
id: finite-positive-definite-window-is-a-relative-corner-selector
kind: claim
title: A finite positive-definite quotient window is an exact relative corner selector
distinct_from:
  induced-rounding-needs-rms-section-fillings: that constructs one particular relative induced corner from Schreier fillings; this identifies the exact finite matrix-order certificate needed for any corner construction, independently of a chosen section.
  authenticated-core-union-basin-is-relative-liftability: that states the moving coordinate-lifting target; this proves a finite-window sufficient criterion and does not assert that the criterion holds for the Iwahori microstates.
  congruence-endpoint-orbits-are-restriction-ring-fibers: that classifies exact representation types after a lift exists; this includes the operator-valued positivity needed to produce a lift.
---

Let \(G\) be a finite group, \(B<G\), and let
\(\beta:B\to U(d)\) be a representation.  Let \(S\subseteq G\) be a
marked generating set and let \(U_s\in U(d)\), \(s\in S\), be prescribed
matrices extending the marked generators of \(\beta\).

Suppose there is a function

\[
F:G\longrightarrow M_d
\]

such that

\[
F(e)=1,\qquad [F(g^{-1}h)]_{g,h\in G}\succeq0,\qquad
F(b)=\beta(b)\quad(b\in B),                              \tag{FPW1}
\]

and

\[
\max_{s\in S}\|F(s)-U_s\|_{2,d}\leq\eta.                 \tag{FPW2}
\]

Then there are a finite-dimensional representation
\(\rho:G\to U(H_\rho)\) and an isometry
\(V:\mathbb C^d\to H_\rho\) satisfying

\[
\rho(b)V=V\beta(b)\quad(b\in B),\qquad
\max_{s\in S}\|V^*\rho(s)V-U_s\|_{2,d}\leq\eta.          \tag{FPW3}
\]

One may take \(\dim H_\rho\leq d|G|\).  Thus (FPW1)--(FPW2) are a
finite semidefinite, operator-valued certificate for an exact relative
finite corner.  No residual finite-dimensionality of an ambient infinite
group is assumed.

Indeed, finite-group positive-definiteness in (FPW1) gives a ucp map

\[
\Theta:C^*(G)\longrightarrow M_d,\qquad
\Theta(u_g)=F(g).                                       \tag{FPW4}
\]

Take its minimal Stinespring dilation
\(\Theta(a)=V^*\rho(a)V\).  Since \(C^*(G)\) is finite-dimensional, the
minimal Stinespring space is finite-dimensional, with the displayed bound.
For \(b\in B\), \(\Theta(u_b)=\beta(b)\) is unitary.  Equality in both
Kadison inequalities puts \(u_b\) in the multiplicative domain of
\(\Theta\), and hence

\[
\rho(b)V=V\beta(b).                                     \tag{FPW5}
\]

This proves (FPW3).

There is also a concrete sufficient way to manufacture the nonrelative
part of the certificate.  Choose unitaries \(W_g\in U(d)\), \(g\in G\),
with \(W_e=1\), and put

\[
\epsilon_s^2={1\over |G|d}\sum_{g\in G}
 \|W_{sg}-U_sW_g\|_F^2.                                 \tag{FPW6}
\]

On \(\ell^2(G)\otimes\mathbb C^d\), let
\(\rho=\lambda_G\otimes1\) and

\[
V\xi=|G|^{-1/2}\sum_{g\in G}e_g\otimes W_g^*\xi .
\]

Then \(V\) is an isometry and

\[
V^*\rho(s)V={1\over |G|}\sum_{g\in G}W_{sg}W_g^*,
\qquad
\|V^*\rho(s)V-U_s\|_{2,d}\leq\epsilon_s.                \tag{FPW7}
\]

Thus vanishing RMS multiplication-table error on one finite quotient is
already enough to produce a finite exact corner.  Relative induction over
\(B\) is the core-preserving refinement recorded in
'induced-rounding-needs-rms-section-fillings'.

Apply this to the authenticated Iwahori core.  If
\(N=\operatorname{ord}(\beta(t))\), then

\[
A_N=PSL_2(\mathbb Z[1/2])/\langle\!\langle t^N\rangle\!\rangle
\]

is finite.  If the prescribed moving tuples admit certificates (FPW1)
with \(G=A_N\), \(B\) the finite core image, and \(\eta_n\to0\), they have
finite-dimensional exact corner dilations.  Property \((T;FD)\), via
'tfd-finite-corner-collapse-and-rfd-firewall', then replaces those
arbitrarily large corners by exact congruence endpoints on
\(d_n+o(d_n)\) dimensions.  Hence this criterion proves
'authenticated-core-union-basin-is-relative-liftability' for that
sequence.

For \(SL_2(\mathbb Z[1/2])\), the finite groups \(A_N\) exist, but the
certificates (FPW1) for the **prescribed** matrices are not presently
known.  Scalar character convergence and the restriction-ring fiber give
only traces and possible exact multiplicities.  They do not give positivity
of the full block matrix in (FPW1), nor the RMS multiplication-table
coherence in (FPW6).  The root problem therefore remains open.
