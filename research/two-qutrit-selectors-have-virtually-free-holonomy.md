---
rg: 2
id: two-qutrit-selectors-have-virtually-free-holonomy
kind: claim
title: Two independent qutrit selectors retain a virtually free full-fibre holonomy model
distinct_from:
  qutrit-matched-prefix-router-family-is-one-finite-hnn-chart: that reuses one rectangular equivalence, so all pair ratios are finite scalar potentials; this allows two independent selector loops and obtains an infinite-order non-scalar relative holonomy.
  qutrit-first-mismatched-prefix-holonomy-is-d8: that realizes a finite dihedral holonomy packet; this realizes the universal relative selector as a Haar unitary with a complete three-by-three Hecke graph on every fibre.
  qutrit-full-leavitt-prefix-conjugator-realizes-phase-star: that constructs one concrete selector and identifies its two hidden escape characters; this proves that adding a second selector conjugacy does not remove either escape character without an additional mixed coefficient relation.
---

**ESTABLISHED UNIVERSAL FIREWALL.** Let \(F\) be any finite qutrit head
containing

\[
 C=\langle J,Z\rangle\cong C_3^2,\qquad h=J^2Z,
\]

and form the two-selector presentation

\[
 \Lambda_2=
 \langle F,u,v\mid uJu^{-1}=h,\ vJv^{-1}=h\rangle.      \tag{TSH1}
\]

Put \(c=vu^{-1}\). Then

\[
 \Lambda_2\cong
 \langle F,u,c\mid uJu^{-1}=h,\ [c,h]=1\rangle.         \tag{TSH2}
\]

This is the fundamental group of a finite graph of finite groups, with
one vertex group \(F\) and two edge groups of order three. Consequently
\(\Lambda_2\) is virtually free and residually finite. The relative
holonomy is nevertheless genuinely non-scalar:

\[
 |c|=\infty,\qquad
 C\cap cCc^{-1}=\langle h\rangle.                       \tag{TSH3}
\]

Let \(\omega\) be a primitive cube root of unity and let \(p_{a,b}\) be
the joint \(C\)-character projection on which

\[
 J=\omega^a,\qquad Z=\omega^b.
\]

In the canonical group trace of \(\Lambda_2\), the complete relative
holonomy table is

\[
 \|p_{a',b'}cp_{a,b}\|_2^2=
 \begin{cases}
  1/27,&2a'+b'=2a+b,\\
  0,&2a'+b'\ne2a+b.
 \end{cases}                                             \tag{TSH4}
\]

Thus \(c\) has a complete three-by-three graph inside every
\(h\)-spectral fibre. The uniform three-cell weight is stationary; no
cell is suppressed.

More strongly, if \(r_\ell\) is the \(\omega^\ell\)-spectral projection
of \(h\), then for every nonzero integer \(k\),

\[
 \tau(r_\ell c^k)=0,\qquad
 \|(c-\zeta)r_\ell\|_2^2=\frac23
 \quad(\zeta\in\mathbb T).                              \tag{TSH5}
\]

Hence the failure is not caused by a scalar or finite holonomy: \(c\)
is Haar on each one-third fibre and stays a fixed distance from every
scalar there.

The two original selectors retain the old Hall leakage exactly. Put

\[
 e_b=p_{1,b},\qquad q=e_0+e_1+e_2,\qquad R=e_0+e_1.
\]

For \(W=u\) or \(W=v\),

\[
 \|(1-q)Wq\|_2^2=\frac29,\qquad
 \|(1-q)WR\|_2^2=\frac4{27}.                            \tag{TSH6}
\]

Each of the two hidden target characters \(p_{0,1}\) and \(p_{2,0}\)
receives squared mass \(1/9\) from \(Wq\), exactly the same mass as the
visible target \(p_{1,2}=e_2\).

These are not merely infinite-dimensional trace values. For every finite
word radius there is a finite quotient of \(\Lambda_2\), injective on the
required ball and on \(F\), whose left regular representation realizes all
relations exactly and matches every displayed moment in that radius.
Thus the two-selector rows, their automatic relation \([c,h]=1\), and
arbitrary fixed finite moment tests admit exact finite-dimensional
countermodels with both hidden sectors present.

For two concrete Leavitt prefix equivalences \(D,D'\), the corresponding
selectors have relative word

\[
 g'g^{-1}=P_h(D'D^{-1})P_h^{-1},
\]

which centralizes \(h\). The theorem proves that non-scalarity, infinite
order, and full fibre mixing of this relative word do not suffice. A
successful continuation must use an additional relation of the explicit
coefficient word \(D'D^{-1}\) which is absent from (TSH1), and must turn
that relation into a normalized-trace imbalance. No such relation is
proved here, so the non-hyperlinearity root remains open.

DERIVATION
bass-serre-two-selector-leakage-proof
