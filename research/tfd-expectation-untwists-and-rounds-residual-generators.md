---
rg: 2
id: tfd-expectation-untwists-and-rounds-residual-generators
kind: route
title: Use the TFD expectation to untwist and round residual generators
target: endpoint-expander-authenticates-bounded-residual-width
requires:
  - tfd-low-leakage-compressions-flexibly-reduce
  - bounded-payload-congruence-tensors-have-uniform-capture
---

# The endpoint commutant is recovered with one uniform constant

Fix one block
\[
 H_j=\mathbb C^{k_j}\otimes H_{\eta_j}.
\]
Conjugation by \(1_{k_j}\otimes\eta_j(g)\) is a finite-dimensional unitary
representation of \(A\) on \(M(H_j)\). Since \(\eta_j\) is irreducible, its
fixed space is
\[
 \mathcal N_j=M_{k_j}\otimes1.                            \tag{1}
\]
Let \(E_j\) be the trace-preserving conditional expectation onto
\(\mathcal N_j\). Property \((T;FD)\), applied exactly as in
**tfd-low-leakage-compressions-flexibly-reduce**, gives
\[
 \|Y-E_j(Y)\|_{2,H_j}^2
 \leq\kappa^{-2}\sum_{g\in Q}
 \|[Y,1\otimes\eta_j(g)]\|_{2,H_j}^2                     \tag{2}
\]
for every \(Y\in M(H_j)\). Amplification by \(M_{k_j}\) creates only extra
fixed vectors and does not change the constant.

Apply (2) to \(Y=Y_{\epsilon,j,s}\). Write
\[
 E_j(Y)=K_{\epsilon,j,s}\otimes1,\qquad
 \delta_{\epsilon,j,s}=\|Y-E_j(Y)\|_{2,H_j}.              \tag{3}
\]
The matrix \(Y\) is unitary. Orthogonality of a conditional expectation and
its contractivity imply that \(K=K_{\epsilon,j,s}\) is a contraction and
\[
 \delta_{\epsilon,j,s}^2
 =1-\|K\|_{2,k_j}^2
 =\operatorname{tr}_{k_j}(1-K^*K).                       \tag{4}
\]
Choose a unitary completion \(V\) of the polar part of \(K\). If
\(\sigma_i(K)\) are its singular values, then
\[
 \|K-V\|_{2,k_j}^2
 =\frac1{k_j}\sum_i(1-\sigma_i(K))^2
 \leq\operatorname{tr}_{k_j}(1-K^*K)
 =\delta_{\epsilon,j,s}^2.                               \tag{5}
\]

# Torsion rounding produces an exact residual vertex

Let \(m_s=2\) for \(s=x\) and \(m_s=3\) for \(s=a\). By (3)--(5),
\[
 \|\pi_{\epsilon,j}(s)-V\otimes\eta_{j,\epsilon}(s)\|_{2,H_j}
 \leq2\delta_{\epsilon,j,s}.                             \tag{6}
\]
Both \(\pi_{\epsilon,j}(s)^{m_s}\) and
\(\eta_{j,\epsilon}(s)^{m_s}\) are the identity. Telescoping the
\(m_s\)-th powers in (6) therefore gives
\[
 \|V^{m_s}-1\|_{2,k_j}
 \leq2m_s\delta_{\epsilon,j,s}.                          \tag{7}
\]
Round the spectrum of \(V\) to the nearest \(m_s\)-th roots of unity.
The resulting unitary \(W_{\epsilon,j,s}\) has
\[
 W_{\epsilon,j,s}^{m_s}=1,\qquad
 \|V-W_{\epsilon,j,s}\|_{2,k_j}
 \leq\|V^{m_s}-1\|_{2,k_j}.                              \tag{8}
\]
Here the pointwise inequality is
\(\operatorname{dist}(z,\mu_{m_s})\leq|z^{m_s}-1|\) on the unit circle.
Equations (6)--(8) yield
\[
 \|\pi_{\epsilon,j}(s)
   -W_{\epsilon,j,s}\otimes\eta_{j,\epsilon}(s)\|_{2,H_j}
 \leq8\delta_{\epsilon,j,s}.                             \tag{9}
\]

The assignments
\[
 \kappa_{j,\epsilon}(x)=W_{\epsilon,j,x},\qquad
 \kappa_{j,\epsilon}(a)=W_{\epsilon,j,a}
\]
define an exact representation of
\(\operatorname{PSL}_2(\mathbb Z)=C_2*C_3\); there are no further vertex
relations. Sum (2) and (9) over the physical block weights. Pythagoras gives
\[
 d_2(\pi,\widehat\pi)
 \leq C_\kappa\Xi,                                       \tag{10}
\]
where \(\widehat\pi\) is (ERW5). This proves (ERW6) and immediately gives
(ERW8).

# The residual edge defect is repaired uniformly at bounded width

Every edge generator is a fixed word in \(x,a\). Fixed-word Lipschitz
continuity and (10) give
\[
 \operatorname{def}(\widehat\pi)
 \leq\operatorname{def}(\pi)+C_\kappa'\Xi.               \tag{11}
\]
Because the endpoint restrictions \(\eta_{j,+}|_B\) and
\(\eta_{j,-}|_B\) agree exactly, no extra edge term appears in (11).
Moreover \(\widehat\pi\) lies in the bounded-payload tensor hull
\(\mathcal H_D\). Hence
**bounded-payload-congruence-tensors-have-uniform-capture** supplies a
compatible endpoint \(\widetilde\pi\) with
\[
 d_2(\widehat\pi,\widetilde\pi)
 \leq C_D
 \bigl(\operatorname{def}(\pi)+C_\kappa'\Xi\bigr)^{\alpha_D}. \tag{12}
\]
Choose \(0<\alpha_D\leq1\). The triangle inequality with (10), followed by
absorption of the linear term on the bounded defect interval, proves
(ERW7).

The proof uses the full finite Kazhdan set only to authenticate a supplied
endpoint factor. It neither selects the congruence representations
\(\eta_j\) nor constructs their common physical block carriers. Those two
selection problems, rather than endpoint spectral-gap collapse or torsion
rounding, are the surviving noncongruence-alignment gate.
