# An involutive twisted double is not covered by the swap proof

Date: 2026-08-13

## The tempting argument

Let \(A\) be a separable MF algebra, \(C\subset A\), and let
\(\alpha\in\operatorname{Aut}(C)\) satisfy \(\alpha^2=1\).  Put

\[
 D_\alpha=A*_{(C,\mathrm{id}),(C,\alpha)}A.
\]

For a faithful representation
\(\pi=\pi_1*_\alpha\pi_2:D_\alpha\to B(H)\), the edge relation is

\[
 \pi_1(c)=\pi_2(\alpha(c)).                         \tag{1}
\]

Set

\[
 \rho_1=\pi_1\oplus\pi_2,\qquad
 \rho_2=\pi_2\oplus\pi_1,
\]

and let \(u\) swap the two summands.  Then
\(\rho_1=u^*\rho_2u\), exactly as in Shulman's proof for an untwisted
double.  It is tempting to conclude that the same proof applies.

## Exact failure

In the untwisted case the common-edge relation gives

\[
 [u,\rho_2(c)]=0.                                    \tag{2}
\]

This is the hypothesis of Shulman's commutant lifting lemma.  In the
twisted case, (1) and \(\alpha^2=1\) give instead

\[
 u^*\rho_2(c)u=\rho_2(\alpha(c)).                    \tag{3}
\]

Thus \(u\) normalizes the edge representation and implements \(\alpha\);
it does not commute with it.

The distinction survives stabilization.  Suppose \(X\) is a contraction
lifting \(u\), and use the usual Halmos unitary

\[
 V=\begin{pmatrix}
 X&(1-XX^*)^{1/2}\\
 (1-X^*X)^{1/2}&-X^*
 \end{pmatrix}.                                      \tag{4}
\]

For a commutant relation, the off-diagonal errors in (4) are commutators
of the defect square roots with two identical copies of a lift of \(c\).
Quasicentrality makes them small.  For (3), the source and target diagonal
entries are lifts of \(c\) and \(\alpha(c)\).  The off-diagonal terms
contain expressions of the form

\[
 (1-XX^*)^{1/2}\bigl(C-C_\alpha\bigr),               \tag{5}
\]

where \(C\) and \(C_\alpha\) lift \(c\) and \(\alpha(c)\), up to the
corresponding left/right placement.  Their quotient value need
not vanish: generally

\[
 \|\rho_2(c)-\rho_2(\alpha(c))\|>0.                  \tag{6}
\]

A quasicentral approximate unit controls commutators with the defect
support; it cannot force (5) to zero when (6) is nonzero.  Doubling once
more merely repackages the same normalizer-lifting problem.

Therefore Shulman's theorem that \(A*_C A\) is MF does not imply that
\(D_\alpha\) is MF, even for an involution \(\alpha\).  The missing input
is precisely an equivariant/normalizer lift:

\[
 V_n^*\phi_n(c)V_n-\phi_n(\alpha(c))\longrightarrow0
 \quad\text{in operator norm}.                       \tag{7}
\]

For the virtually-cyclic central-radical shear, (7) is the antipodal
spectral condition on the primitive radical word.  Proving it would make
the twisted double operator-MF and would yield a hyperlinear nonsofic group;
assuming it is exactly the unresolved step.
