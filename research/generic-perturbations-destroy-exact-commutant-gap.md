---
rg: 2
id: generic-perturbations-destroy-exact-commutant-gap
kind: claim
title: Trace-faithful generic perturbations destroy the Poincare gap to the literal commutant
artifacts:
  - research/regular-quotient-perturbation-defeats-literal-poincare.md
distinct_from:
  el-r-polynomial-robust-spectral-gap: that gives a robust low-spectrum gap for almost representations of a property-T group; this proves that the low-energy band need not equal the kernel of the actual generator Laplacian.
  kazhdan-stabilizer-collapses-shared-pauli-sign: that projects root Pauli unitaries into the commutant of a genuine actor representation; this shows that exactness is load-bearing and the same projection is unavailable for arbitrary almost actors.
  approximate-collapse-for-kt-compressor: that asks for a source-specific commutant/image-collapse theorem in a matrix ultraproduct; this refutes only the naive relator-defect-to-literal-coordinate-commutant route, not that source-specific claim.
---

Let \(\Gamma\) be an infinite finitely generated residually finite group
with a generating tuple \(S=(s_1,\ldots,s_k)\), \(k\ge2\). This includes
the Kun--Thom polynomial elementary vertex
\[
 \Gamma=EL_r(\mathbb F_q[x_1,\ldots,x_d]),\qquad r\ge3.
\]

There exist trace-faithful asymptotic unitary representations
\[
 \theta_n:\Gamma\longrightarrow U(D_n)
\]
and unitaries \(A_n\in U(D_n)\) such that
\[
 \max_{s\in S}\|[A_n,\theta_n(s)]\|_2\longrightarrow0,   \tag{GPG1}
\]
but
\[
 \theta_n(S)'=\mathbb C I_{D_n},\qquad
 \operatorname{dist}_2(A_n,\theta_n(S)')=1              \tag{GPG2}
\]
for all sufficiently large \(n\).

The construction is maximally close to genuine coordinates. There are
genuine regular finite-quotient representations
\[
 \rho_n:\Gamma\to U(D_n)
\]
and numbers \(\varepsilon_n\downarrow0\) such that
\[
 \max_{s\in S}\|\theta_n(s)-\rho_n(s)\|_{\mathrm{op}}
 <\varepsilon_n.                                        \tag{GPG3}
\]
Consequently every fixed relator, every fixed multiplication row, and every
fixed group word has defect \(O(\varepsilon_n)\), while
\[
 \operatorname{tr}_{D_n}(\theta_n(g))\longrightarrow0
 \qquad(g\ne1).                                         \tag{GPG4}
\]

Thus no dimension-independent modulus can have the form
\[
 \operatorname{dist}_2(X,\{U_s:s\in S\}')
 \le\omega\!\left(
   \max_s\|[X,U_s]\|_2+\operatorname{Def}(U)
 \right),
 \qquad \omega(t)\to0,                                  \tag{GPG5}
\]
even when \(X\) is unitary, the almost representations are trace-faithful,
and their generators are operator-norm perturbations of genuine
representations.

Equivalently, an Ozawa finite sum-of-squares certificate cannot force
Poincare distance to the literal commutant of the actual generator
matrices. It can force concentration in a low-energy spectral band of the
approximate conjugation Laplacian. In this construction the literal-kernel-orthogonal unitary
\(A_n\) has Rayleigh quotient tending to zero, so the low band has
nonzero mass outside the literal kernel.

The theorem does not refute a source-specific propagation argument using
the full shared-center or Kun--Thom relations. It proves that relator
defects plus property \((T)\) alone cannot replace the exact-actor
hypothesis. No nonhyperlinear group is proved here.

DERIVATION
regular-quotient-perturbation-defeats-literal-poincare
