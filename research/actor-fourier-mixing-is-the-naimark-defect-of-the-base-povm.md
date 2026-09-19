---
rg: 2
id: actor-fourier-mixing-is-the-naimark-defect-of-the-base-povm
kind: claim
title: Actor Fourier mixing is exactly the Naimark defect of the base POVM
distinct_from:
  naimark-stinespring-keeps-the-synchbcs-pauli-corner-gate: that proves a general sharp-compression multiplicative-domain theorem; this derives every Fourier coefficient equation in an algebraic crossed product and quantifies the exact actor mass needed to cancel the marked quarter overlap.
  leavitt-root-signs-cannot-host-the-perfect-synchbcs: that proves the base-only and root-sign firewalls; this treats genuinely mixed finite actor Fourier sums in the full negative Kun--Thom corner.
  shared-center-extraspecial-wreath-has-fd-invisible-spin-sector: that identifies the negative base as a UHF spin algebra and the actor-normalizer multiplicity; this classifies the identity-coefficient defect of arbitrary algebraic PVMs in its crossed product.
  hecke-zero-compression-has-fixed-density-bass-serre-absorber: that constructs one finite D8 zero-compression cell; this shows abstractly that every one-context actor cancellation is a Naimark dilation and records the coefficient movement needed before any cancellation is possible.
artifacts:
  - research/crossed-product-pvm-coefficient-gram-and-quarter-bound-proof.md
---

**ESTABLISHED MIXED-FOURIER FIREWALL; NO NONHYPERLINEAR GROUP IS
CLAIMED.**

Let \((B,\tau)\) be a unital tracial star algebra faithfully represented in a
finite von Neumann algebra, let a group \(G\) act by trace-preserving star
automorphisms \(\alpha_g\), and work in the algebraic crossed product
\(B\rtimes_{\mathrm{alg}}G\). Suppose

\[
 P_i=\sum_{g\in G}a_{i,g}u_g\qquad(1\leq i\leq m)
 \tag{AFM1}
\]

is a finite-support PVM. Put \(A_i=a_{i,1}=E_B(P_i)\). Then
\((A_i)\) is a POVM in \(B\), and its complete defect kernel is the Gram
matrix of the nonidentity actor coefficients:

\[
 \boxed{\quad
 \delta_{ij}A_i-A_iA_j
   =\sum_{g\ne1}a_{i,g}a_{j,g}^* .
 \quad}                                                     \tag{AFM2}
\]

In particular,

\[
 A_i-A_i^2=\sum_{g\ne1}a_{i,g}a_{i,g}^*,
 \qquad
 \sum_{g\ne1}\|a_{i,g}\|_2^2=\tau(A_i-A_i^2).               \tag{AFM3}
\]

Thus \(A_i\) is a projection if and only if \(P_i=A_i\) is base-only. An
actor Fourier tail cannot alter a sharp named base projection while retaining
it as the identity coefficient.

For two orthogonal projections \(P,Q\), with identity coefficients \(A,B\),

\[
 \tau(AB)\leq
 \sqrt{\tau(A-A^2)\tau(B-B^2)}.                             \tag{AFM4}
\]

Apply this in the negative shared-center Clifford corner to the two commuting
root cuts \(Q_e,Q_f\) with
\(\tau(Q_eQ_f)=1/4\). If

\[
 \|A-Q_e\|_2\leq\varepsilon_e,\qquad
 \|B-Q_f\|_2\leq\varepsilon_f,
\]

then orthogonality of \(P,Q\) forces

\[
 \frac14-\varepsilon_e-\varepsilon_f
 \leq3\sqrt{\varepsilon_e\varepsilon_f}.                   \tag{AFM5}
\]

In particular, if both errors are at most \(\varepsilon\), then
\(\varepsilon\geq1/20\). Hence actor coefficients can cancel the fixed
quarter overlap only after a dimension-independent movement of the sharp
base ports.

The bound has a finite absorber at the opposite extreme. In
\(\mathbf C[C_2]\), for its generator \(u\),

\[
 P_\pm=\frac{1\pm u}{2}
\]

are orthogonal, while both identity coefficients are \(1/2\); their
offidentity coefficients cancel the base overlap \(1/4\) exactly. This is a
two-dimensional model. More generally, one PVM and its identity-coefficient
POVM are only a finite Naimark cell; nonmatricial content can begin only when
several contexts share the same unsharp base effects and their actor
coefficients are coupled by a non-finitely-completable return pattern.

For the full Kun--Thom negative corner

\[
 p_-\mathbf C[E(X)\rtimes G]p_-
 \cong
 \left(p_-\mathbf C[E(X)]p_-\right)\rtimes_{\mathrm{alg}}G,
\]

the exact residual gate is therefore sharper than "use an actor term":

1. no source port may retain a named Pauli/root projection as its exact
   identity coefficient;
2. the shared identity coefficients must instead form compatible unsharp
   POVMs separated from those root ports at fixed \(2\)-norm scale;
3. the nonidentity Fourier rows must realize (AFM2) simultaneously across
   all contexts and consume the Kun--Thom marked compressor pattern, rather
   than a finite actor cell.

Equations (AFM2)--(AFM5) are necessary, not sufficient. No such global
mixed-context atlas is constructed here, and Cairn remains OPEN.

DERIVATION
crossed-product-pvm-coefficient-gram-and-quarter-bound-proof
