---
rg: 2
id: right-translation-flattens-every-relative-kraus-frame
kind: claim
title: Right-translation amplification flattens every relative Kraus frame to isometries
artifacts:
  - research/amplify-right-translates-and-preserve-frame-energy.md
distinct_from:
  multi-kraus-frame-energy-is-the-full-relative-pd-gate: that parametrizes the full body by arbitrary rectangular components; this proves every such component family can be replaced by pointwise isometries without changing its table or energy.
  gram-flat-kraus-frames-polarize-to-unitary-tables: that turns square almost-unitary fibres into unitaries on the original dimension; this produces exact tall isometries and isolates target-dimension reduction as the remaining unitary gap.
  every-relative-ucp-window-lives-in-one-induced-representation: that minimizes ambient representation multiplicity; this permits a larger right-translate amplification in exchange for exact pointwise flatness.
---

Let \(A_g:\mathbb C^d\to\mathbb C^r\) be any relative Stinespring frame
satisfying (MKF2). Define
\[
 \widetilde A_g:\mathbb C^d\longrightarrow
 \bigoplus_{h\in G}\mathbb C^r,\qquad
 \widetilde A_g\xi
 =|G|^{-1/2}\bigl(A_{gh}\xi\bigr)_{h\in G}.             \tag{RTF1}
\]
Then
\[
 \widetilde A_g^*\widetilde A_g=|G|^{-1}1
 \quad\hbox{for every }g,                               \tag{RTF2}
\]
\[
 \widetilde A_{bg}=\widetilde A_g\beta(b)^*,            \tag{RTF3}
\]
and the complete coefficient function and marked energy are unchanged:
\[
 F_{\widetilde A}(k)=F_A(k)\quad(k\in G),\qquad
 \mathcal E_U^{\rm K}(\widetilde A)
 =\mathcal E_U^{\rm K}(A).                              \tag{RTF4}
\]

Equivalently, put \(V_g=|G|^{1/2}\widetilde A_g\). The full relative
positive-definite body consists exactly of
\[
 F_V(k)=\frac1{|G|}\sum_gV_{kg}^*V_g                    \tag{RTF5}
\]
where \(V_g:\mathbb C^d\to\mathbb C^R\) range over isometries, for an
arbitrary common finite \(R\), satisfying
\[
 V_{bg}=V_g\beta(b)^*.                                  \tag{RTF6}
\]
Moreover the exact full-PD energy may be written
\[
 e_{\rm iso}(U)
 =\inf_V\left(
  \frac1{|S||G|}\sum_{s,g}
  \|V_{sg}U_s-V_g\|_{2,d}^2\right)^{1/2}
 =e_{\rm K}(U).                                         \tag{RTF7}
\]
Thus
\[
 \Delta(U)\leq e_{\rm iso}(U)
 \leq\sqrt{\Delta(U)^2+2\Delta(U)}.                     \tag{RTF8}
\]

A relative unitary zero-cochain is precisely the special case
\(R=d\), with \(V_g=W_g^*\). Therefore arbitrary Kraus nonflatness is not
an obstruction to an isometry-valued synchronization theorem: it can
always be removed by the explicit amplification (RTF1). The construction
itself may enlarge \(R\) by the moving factor \(|G|\), so it does not
supply unitaries on the original carrier or an \(o(d)\)-dimensional
completion.

The additional common-corange step is now supplied, on every uniformly
expanding quotient family, by
cayley-expansion-aligns-isometry-frame-coranges. If the Cayley Poincare
gap is \(\gamma\), that theorem converts every isometry frame of energy
\(e\) to a relative unitary table of energy at most
\[
 \left(1+2\sqrt{2/\gamma}\right)e.
\]
Property \((T;FD)\) makes \(\gamma\) uniform on the authenticated finite
quotients. Thus unitary synchronization and the full multi-Kraus gate are
quantitatively equivalent in the concrete Iwahori family. What remains
open is the nonlinear estimate forcing either energy to vanish from the
two cubic presentation defects; no such estimate is proved here.

DERIVATION
amplify-right-translates-and-preserve-frame-energy
