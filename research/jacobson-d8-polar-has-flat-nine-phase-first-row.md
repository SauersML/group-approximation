---
rg: 2
id: jacobson-d8-polar-has-flat-nine-phase-first-row
kind: claim
title: Each D8 polar branch has a flat qutrit first row
artifacts:
  - research/jacobson-d8-polar-qutrit-block-table-proof.md
distinct_from:
  jacobson-d8-spectral-polar-splits-residual-without-qutrit-selection: that computes the full range marginals and the degree-four packet covariance; this resolves every individual qutrit phase block and its ordered raw-T covariance.
  qutrit-shortest-tk-word-graphs-are-diagonal-or-complete: that classifies the bare group-word blocks in the dihedral subgroup; this computes the blocks after the exact residual polar is inserted.
  qutrit-jacobson-residual-has-fixed-polar-gap: that gives the terminal norm gap if a one-complement covariance is authenticated; this proves that the D8 polar supplies no such covariance.
---

Let
\[
 C=\langle J,Z_1\rangle\cong C_3^2,\qquad
 e_a=z_{C,\chi_a},\quad
 \chi_a(J)=\omega,\quad\chi_a(Z_1)=\omega^a,
\]
where \(a\in\mathbb F_3\).  Thus
\[
 q=e_0+e_1+e_2,\qquad R=e_0+e_1,\qquad q-R=e_2.
\]
For the residual projection \(e=e_{\rm res}\), the raw root
\(t=x_{23}(T)\), the opposite scalar root \(k=x_{31}(1)\), and
\(\eta\in\{+1,-1\}\), put
\[
 V_\eta=\sqrt2\,{1+\eta t\over2}\,ke,\qquad
 W_{a,\eta}=e_aV_\eta e=e_aV_\eta.
\]

Every one of the six first-row blocks is nonzero, and
\[
 \|W_{a,\eta}\|_2^2={1\over288}
 \qquad(a\in\mathbb F_3,\ \eta=\pm1).                 \tag{JQB1}
\]
Their exact ordered covariance table is
\[
\begin{array}{c|c|c|c|c}
 a&\|W_{a,\eta}\|_2^2&JW_{a,\eta}&Z_1W_{a,\eta}
   &e_atV_\eta\\ \hline
 0&1/288&\omega W_{0,\eta}&W_{0,\eta}&\eta W_{0,\eta}\\
 1&1/288&\omega W_{1,\eta}&\omega W_{1,\eta}&\eta W_{1,\eta}\\
 2&1/288&\omega W_{2,\eta}&\omega^2 W_{2,\eta}&\eta W_{2,\eta}.
\end{array}                                                    \tag{JQB2}
\]
The last column is deliberately ordered as \(e_atV_\eta\).
In general \(t\) does not commute with \(e_a\), so it is not a claim that
\(tW_{a,\eta}=\eta W_{a,\eta}\).

More strongly, if \(z_{\rho,a}\), \(\rho,a\in\mathbb F_3\), are all nine
character atoms of \(C\), then
\[
 \|z_{\rho,a}V_\eta\|_2^2={1\over288},\qquad
 \sum_{\rho,a}(z_{\rho,a}V_\eta)^*(z_{\rho,a}V_\eta)=e. \tag{JQB3}
\]
Thus each sign branch is flat across the complete nine-phase spectrum, not
only across the selected central-\(\omega\) row.

Within that row, the bare \(t\)-word phase graph is also balanced.  If the
outer coordinates \(2,3\) have different \(u_1\)-labels, all nine blocks
\(e_bt e_a\) are nonzero and have squared norm \(1/81\).  If they have the
same label, or one is the extra fixed coordinate, only the diagonal blocks
are nonzero and they have squared norm \(1/27\).  The two possible neighbor
sets for \(\{e_0,e_1\}\) therefore have size three and two, respectively,
never one.

In particular
\[
 \|RV_\eta\|_2^2={1\over144},\qquad
 \|(q-R)V_\eta\|_2^2={1\over288}.                       \tag{JQB4}
\]
The expected \(2:1\) marginal is present, but the polar has no support zero
and no typed incidence sending both selected phases only through the one
complement phase.  The exact D8 polar is therefore a rigorous balanced
no-go for the first qutrit row.  A Hall-deficient continuation must add a
mixed occurrence outside this polar and its shortest \(t,k\) word graph.
