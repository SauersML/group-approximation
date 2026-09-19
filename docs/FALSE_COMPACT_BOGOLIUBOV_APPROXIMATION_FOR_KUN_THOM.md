# Compact representations cannot quantize the Kun--Thom coset mode

Date: 2026-08-13

## Result

Let \(\Gamma<G\), and write

\[
 P_\Gamma=\{t\in G:t\Gamma t^{-1}\leq \Gamma\}.
\]

Assume that \(P_\Gamma\) generates \(G\).  For every homomorphism
\(\rho:G\to K\) into a compact group,

\[
 \overline{\rho(\Gamma)}\triangleleft \overline{\rho(G)}.
 \tag{1}
\]

Indeed, put \(H=\overline{\rho(\Gamma)}\).  If \(t\in P_\Gamma\), then
\(\rho(t)H\rho(t)^{-1}\subseteq H\).  The two compact groups in this
inclusion need not have positive measure in the ambient compact group, so a
Haar-measure argument is not sufficient.  Instead use recurrence.  In the
compact closure of \(\rho(G)\), choose positive integers \(n_j\to\infty\)
such that \(\rho(t)^{n_j}\to1\).  If \(h\in H\), then

\[
 \rho(t)^{n_j-1}h\rho(t)^{-(n_j-1)}\in H
\]

because conjugation by \(\rho(t)\) maps \(H\) into itself.  The displayed
elements converge to \(\rho(t)^{-1}h\rho(t)\).  Closedness of \(H\) gives
\(\rho(t)^{-1}H\rho(t)\subseteq H\), which is the reverse inclusion after
conjugating.  Hence \(\rho(t)H\rho(t)^{-1}=H\).
Thus every \(\rho(t)\), \(t\in P_\Gamma\), normalizes \(H\), proving (1).

Consequently, for every finite-dimensional unitary representation \(\rho\)
of \(G\),

\[
 (\mathcal H_\rho)^\Gamma=(\mathcal H_\rho)^H
\]

is a \(G\)-invariant subspace.  In particular a \(\Gamma\)-fixed vector in
a finite-dimensional representation cannot have a nonzero component which
is moved out of the \(\Gamma\)-fixed space by an ambient compressor.

## Application to the Clifford route

In the Kun--Thom pair, \(\Gamma\) is infranormal, nonnormal, and has
property \((T)\).  The
quasi-regular representation

\[
 \lambda_{G/\Gamma}:G\to O(\ell^2(G/\Gamma))
\]

contains the \(\Gamma\)-fixed vector \(\delta_\Gamma\).  Since \(\Gamma\)
is not normal, choose \(g\in G\) and \(h\in\Gamma\) with
\(g^{-1}hg\notin\Gamma\).  Then

\[
 \langle\lambda_{G/\Gamma}(g^{-1}hg)\delta_\Gamma,
          \delta_\Gamma\rangle=0.                    \tag{2}
\]

This pointed representation cannot be weakly approximated by
finite-dimensional representations.  Otherwise choose unit vectors
\(\xi_n\) in finite-dimensional representations \(\rho_n\) whose matrix
coefficients converge to those of \(\delta_\Gamma\) on the finite set
consisting of a Kazhdan set for \(\Gamma\) and \(g^{-1}hg\).  Property
\((T)\) supplies \(\Gamma\)-fixed vectors \(\eta_n\) with
\(\|\xi_n-\eta_n\|\to0\).  By (1), the \(\Gamma\)-fixed space of each
\(\rho_n\) is \(G\)-invariant, so

\[
 \rho_n(g^{-1}hg)\eta_n=eta_n.
\]

Its coefficient therefore tends to one, contradicting (2).  Thus the
distinguished coset mode has behavior forbidden not only in each exact
finite-dimensional representation but also in their pointed weak closure.

This closes the proposed construction of

\[
 \operatorname{Cl}(G/\Gamma)\rtimes G
\]

by approximating \(\lambda_{G/\Gamma}\) with finite-dimensional orthogonal
representations and applying fermionic second quantization.  Any successful
Connes-embedding must be genuinely ultraproduct-level: it cannot arise from
finite-dimensional representations converging to the quasi-regular first
chaos.

The obstruction does not itself prove non-embeddability.  Hilbert--Schmidt
almost-representations need not be close to honest finite-dimensional
representations; controlling exactly that escape is the matrix analogue of
the Kun--Thom component theorem.
