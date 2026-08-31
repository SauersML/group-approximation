---
rg: 2
id: binary-cubic-curl-has-global-torus-hecke-blocks
kind: claim
title: Binary cubic curl has exact global right-torus Hecke blocks
distinct_from:
  proper-torus-label-cover-has-dihedral-monodromy: that rules out a fiberwise cyclic deck decomposition; this uses the genuine global right-torus symmetry which moves base cosets and triangle rows together.
  right-u-reynolds-has-torus-hecke-blocks: that treats the complex signed tangent column and its right-unipotent-fixed principal series; this gives the characteristic-two blocks of the nonlinear diagonal parity code.
  diagonal-exact-inversion-is-two-cubic-parity-code: that identifies the binary syndrome abstractly; this writes every global torus block as an explicit three-phase Hecke matrix.
---

Let \(G=\operatorname{PSL}_2(\mathbb F_p)\), let
\[
 N=\langle h(2),x\rangle,\qquad A=\langle a\rangle,
 \qquad B=\langle b\rangle,
\]
where \(a=xt\) and \(b=xt^2r\), and let \(T_s\) be the full projective
split torus. Over a field \(k\) of characteristic two, write
\[
 C^1=k[N\backslash G],\qquad
 C^2=k[A\backslash G]\oplus k[B\backslash G].
\]
The binary cubic curl is
\[
 (\delta_af)(Ag)=\sum_{j=0}^2 f(Na^{-j}g),\qquad
 (\delta_bf)(Bg)=\sum_{j=0}^2 f(Nb^{-j}g),              \tag{BTH1}
\]
\[
 \delta_1=(\delta_a,\delta_b).
\]
It commutes exactly with right translation by \(T_s\).

Assume first that \(m=|T_s|\) is odd, and extend scalars to a splitting
field \(\mathbb E\) for \(C_m\) over \(k\). For
\(\chi\in\widehat{T_s}(\mathbb E)\), put
\[
 P_\chi=m^{-1}\sum_{s\in T_s}\chi(s)^{-1}R_s.           \tag{BTH2}
\]
Then
\[
 C^1_{\mathbb E}=\bigoplus_\chi C^1_\chi,\qquad
 C^2_{\mathbb E}=\bigoplus_\chi C^2_\chi,\qquad
 \delta_1=\bigoplus_\chi\delta_{1,\chi}.                \tag{BTH3}
\]

There is an explicit Mackey basis for every block. For
\(z\in N\backslash G/T_s\), define
\[
 T_z=T_s\cap z^{-1}Nz.
\]
The orbit \(NzT_s\) contributes one coordinate to \(C^1_\chi\) exactly
when \(\chi|_{T_z}=1\). The analogous rule for
\(y\in A\backslash G/T_s\) or \(B\backslash G/T_s\) gives the output
coordinates. In those bases,
\[
 (\delta_{a,\chi})_{y,z}
 =\sum_{\substack{0\leq j\leq2\\
                   a^{-j}y\in NzT_s}}
   \chi(s_{j,y,z})^{-1},                                \tag{BTH4}
\]
where \(a^{-j}y=nzs_{j,y,z}\) with \(n\in N\); the stabilizer condition
makes the phase well defined. The formula for
\(\delta_{b,\chi}\) is identical with \(a,A\) replaced by \(b,B\).
Thus every entry is a sum of at most three explicit torus phases.

The right-\(U\)-fixed part, where \(U=\langle t\rangle\), is the usual
principal-series slice:
\[
 (C^1_\chi)^U\cong
 \left(\operatorname{Ind}_{T_sU}^{G}\chi^{-1}\right)^N. \tag{BTH5}
\]
It is a reducing slice of (BTH3), but it is not the whole binary
cochain space.

If \(m=2^\nu m_0\) with \(m_0\) odd, the odd-character blocks survive in
the semisimple quotient and each carries a length-\(2^\nu\) radical
filtration. This follows from
\[
 k[C_m]\cong k[z]/((z^{m_0}-1)^{2^\nu}).                \tag{BTH6}
\]
The curl commutes with the global right action, so unlike the fiberwise
label evaluation it preserves this filtration.

Equations (BTH3)--(BTH6) are an exact finite block reduction. They do not
supply a uniform Hamming decoder: ranks and singular values after a
characteristic-zero lift need not control the characteristic-two code,
and the principal-series slice does not exhaust \(C^1\). A modular
rank/cosystolic estimate uniform in every block and every radical layer
is still required. The root remains open.

DERIVATION
binary-global-torus-hecke-block-proof
