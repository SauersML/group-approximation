---
rg: 2
id: binary-global-torus-hecke-block-proof
kind: route
title: Apply Mackey orbit Fourier analysis to the characteristic-two cubic incidence map
target: binary-cubic-curl-has-global-torus-hecke-blocks
requires:
  - diagonal-exact-inversion-is-two-cubic-parity-code
  - diagonal-parity-is-hecke-but-tau-misses-local-links
  - proper-torus-label-cover-has-dihedral-monodromy
---

Right translation commutes with every left translation. Hence for
\(s\in T_s\),
\[
 \delta_aR_s=R_s\delta_a,\qquad
 \delta_bR_s=R_s\delta_b.                              \tag{BTP1}
\]
The sums in (BTH1) are invariant under replacing \(g\) by \(a^kg\) or
\(b^kg\), respectively, so they are well defined on the stated output
cosets. This proves that \(\delta_1\) is a map of right
\(k[T_s]\)-modules.

When \(m\) is odd, Maschke's theorem and scalar extension to a splitting
field give the orthogonal idempotents (BTH2). Equation (BTP1) implies
\(\delta_1P_\chi=P_\chi\delta_1\), proving (BTH3).

For the Mackey coordinates, the right \(T_s\)-orbit through \(Nz\) is
\(NzT_s\), with stabilizer
\[
 T_z=\{s:Nzs=Nz\}=T_s\cap z^{-1}Nz.
\]
The \(\chi\)-eigenline on this orbit exists exactly when
\(\chi|_{T_z}=1\). Choose its basis function to be
\[
 e_{z,\chi}(nzs)=\chi(s)^{-1}
\]
on \(NzT_s\), and zero elsewhere. The stabilizer condition makes this
definition independent of the expression \(nzs\). The same construction
on \(A\backslash G\) and \(B\backslash G\) gives the output bases.

Evaluate the first row at an output representative \(y\):
\[
 (\delta_ae_{z,\chi})(Ay)
 =\sum_{j=0}^2e_{z,\chi}(Na^{-j}y).
\]
A summand vanishes unless \(a^{-j}y\in NzT_s\); if
\(a^{-j}y=nzs_{j,y,z}\), it equals
\(\chi(s_{j,y,z})^{-1}\). This proves (BTH4), and the second row is
identical.

Right \(U\)-invariance adds the condition \(f(gu)=f(g)\). Together with
the right \(T_s\)-eigencondition, this is the standard right-covariant
model induced from the Borel \(T_sU\); inversion of the argument converts
it to the usual left-covariant principal series. Left \(N\)-invariance
takes its \(N\)-fixed subspace, proving (BTH5).

Finally, if \(m=2^\nu m_0\), then in characteristic two
\[
 z^m-1=(z^{m_0}-1)^{2^\nu}.
\]
Because \(m_0\) is odd, \(z^{m_0}-1\) is square free. The ideal it
generates is therefore the radical of \(k[C_m]\), with nilpotence length
\(2^\nu\); the semisimple quotient has the odd-character decomposition.
Since (BTP1) makes \(\delta_1\) a module map, it sends every radical power
of the input into the corresponding radical power of the output. This
proves (BTH6) and completes the exact block ledger.
