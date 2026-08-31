---
rg: 2
id: regular-quotient-perturbation-defeats-literal-poincare
kind: route
title: Perturb regular quotient generators generically while retaining a right-regular almost invariant
target: generic-perturbations-destroy-exact-commutant-gap
requires:
  - el-r-polynomial-robust-spectral-gap
  - kazhdan-stabilizer-collapses-shared-pauli-sign
  - approximate-collapse-for-kt-compressor
---

# Perturb regular quotient generators generically while retaining a right-regular almost invariant

All Hilbert--Schmidt norms are normalized.

## 1. Residual regular coordinates

Choose a nested residual chain
\[
 \Gamma=N_0\ge N_1\ge\cdots,\qquad
 [\Gamma:N_n]<\infty,\qquad
 \bigcap_nN_n=\{1\}.
\]
Put
\[
 Q_n=\Gamma/N_n,\qquad D_n=|Q_n|,
\]
and let
\[
 \rho_n:\Gamma\longrightarrow U(\ell^2(Q_n))
\]
be the left regular representation of the quotient.

For the Kun--Thom polynomial elementary group, residual finiteness is
elementary. A nonidentity matrix has a nonzero polynomial entry after
subtracting the identity. Specialize the polynomial ring to a suitable
finite extension of \(\mathbb F_q\) on which that entry remains nonzero.
The resulting finite matrix group detects the element. A diagonal
intersection gives the chain above.

Fix \(h\ne1\) in \(\Gamma\). For all sufficiently large \(n\), its image
\(\bar h_n\in Q_n\) is nontrivial. Let
\[
 A_n=R_{\bar h_n}
\]
be right translation by \(\bar h_n\). Left and right translations commute,
so
\[
 [A_n,\rho_n(s_i)]=0\qquad(1\le i\le k).                 \tag{1}
\]
Moreover \(A_n\) is unitary and
\[
 \operatorname{tr}_{D_n}(A_n)=0.                        \tag{2}
\]

## 2. Irreducible tuples are dense

We use the following finite-dimensional fact.

**Lemma.** If \(D\ge2\) and \(k\ge2\), then tuples
\[
 (U_1,\ldots,U_k)\in U(D)^k
\]
whose common commutant is \(\mathbb C I_D\) are dense.

To see this, perturb the first entry so that it has simple spectrum. In
an eigenbasis for that entry, every operator in its commutant is diagonal.
Perturb the second unitary so that all its off-diagonal matrix entries in
that basis are nonzero. A diagonal matrix commuting with the second entry
must have all diagonal entries equal. Further tuple entries are irrelevant.
Both required perturbations can be arbitrarily small: simple-spectrum
unitaries are dense, and the vanishing of any specified matrix entry is a
proper real-algebraic condition in \(U(D)\).

Choose any sequence \(\varepsilon_n\downarrow0\). Apply the lemma inside
the operator-norm \(\varepsilon_n\)-neighborhood of the exact tuple
\[
 (\rho_n(s_1),\ldots,\rho_n(s_k)).
\]
We obtain unitaries \(U_{i,n}\) satisfying
\[
 \|U_{i,n}-\rho_n(s_i)\|_{\mathrm{op}}<\varepsilon_n,
 \qquad
 \{U_{1,n},\ldots,U_{k,n}\}'=\mathbb C I_{D_n}.           \tag{3}
\]

This is the only genericity input. No perturbation is made to \(A_n\).

## 3. The perturbed tuple is a trace-faithful asymptotic representation

For each \(g\in\Gamma\), fix once and for all a word
\[
 w_g=w_g(s_1^{\pm1},\ldots,s_k^{\pm1})
\]
representing it, with \(w_1\) empty. Define
\[
 \theta_n(g)=w_g(U_{1,n},\ldots,U_{k,n}).                 \tag{4}
\]
Telescoping products of unitaries and (3) give
\[
 \|\theta_n(g)-\rho_n(g)\|_{\mathrm{op}}
 \le |w_g|\varepsilon_n.                                \tag{5}
\]
Hence, for fixed \(g,h\),
\[
\begin{aligned}
 \|\theta_n(g)\theta_n(h)-\theta_n(gh)\|_2
 &\le
 \|\theta_n(g)-\rho_n(g)\|_2\\
 &\quad+\|\theta_n(h)-\rho_n(h)\|_2
 +\|\theta_n(gh)-\rho_n(gh)\|_2\\
 &\longrightarrow0.                                    \tag{6}
\end{aligned}
\]
Thus \((\theta_n)\) is an asymptotic representation. The same telescoping
estimate says that a fixed relator of length \(L\) has even operator-norm
defect at most \(L\varepsilon_n\).

If \(g\ne1\), residuality gives \(g\notin N_n\) eventually. Nonidentity
left translation in a regular representation has normalized trace zero,
so (5) gives
\[
 |\operatorname{tr}_{D_n}(\theta_n(g))|
 \le |w_g|\varepsilon_n\longrightarrow0.                 \tag{7}
\]
This proves trace-faithfulness.

## 4. An almost-central unitary remains distance one from the literal commutant

Equation (1) and (3) give
\[
\begin{aligned}
 \|[A_n,U_{i,n}]\|_2
 &\le
 \|A_n(U_{i,n}-\rho_n(s_i))\|_2\\
 &\quad+
 \|(U_{i,n}-\rho_n(s_i))A_n\|_2\\
 &\le2\varepsilon_n.                                    \tag{8}
\end{aligned}
\]
On the other hand, the actual generator commutant is scalar by (3). The
orthogonal projection of \(A_n\) onto the scalars is
\(\operatorname{tr}_{D_n}(A_n)I=0\), by (2). Consequently
\[
 \operatorname{dist}_2(A_n,\theta_n(S)')
 =\operatorname{dist}_2(A_n,\mathbb C I)
 =\|A_n\|_2=1.                                          \tag{9}
\]
Equations (5), (8), and (9) prove (GPG1)--(GPG4) and refute every modulus
of the form (GPG5).

## 5. What happens to the approximate Laplacian

Let
\[
 \mathcal L_n
 =\sum_{i=1}^k
 (I-\operatorname{Ad}U_{i,n})^*
 (I-\operatorname{Ad}U_{i,n})
\]
on \(L^2(M_{D_n})\). It is positive and
\[
 \ker\mathcal L_n
 =\{U_{1,n},\ldots,U_{k,n}\}'
 =\mathbb C I.                                          \tag{10}
\]
The trace-zero unit vector \(A_n\) is orthogonal to this kernel, but (8)
gives
\[
 \langle A_n,\mathcal L_n A_n\rangle
 =\sum_i\|[A_n,U_{i,n}]\|_2^2
 \le4k\varepsilon_n^2.                                  \tag{11}
\]
Therefore the least positive eigenvalue of \(\mathcal L_n\) is at most
\(4k\varepsilon_n^2\), even though \(\Gamma\) may have property \((T)\).

There is no conflict with an Ozawa sum-of-squares certificate or with
property \((T;\mathrm{FD})_{\mathrm{rob}}\). Under an almost
representation, the certificate allows a cluster of eigenvalues tending
to zero and separates that low band from the rest of the spectrum. In the
present construction the low band is a perturbation of the large
right-regular commutant of \(\rho_n(\Gamma)\); generic perturbation moves
it off eigenvalue zero while the literal kernel collapses to the scalars.
The certificate controls the band, not equality of that band with (10).

## 6. Remaining source-specific possibility

The counterexample uses only actor generators, their relators, and one
almost-central unitary. It does not impose the second Pauli generator,
the common commutator sign, or uniform cross-site rows. Those extra rows
could in principle force the low spectral band to propagate coherently.
Accordingly this is not a counterexample to the full shared-center
presentation or to approximate Kun--Thom image collapse.

It does close the proposed shortcut: no finite sum-of-squares argument
depending only on stabilizer relator defects and root commutator defects
can replace the exact conditional expectation in the exact-actor proof.
The remaining issue is precisely propagation of the robust low band
through the ambient actor and its double cosets.
