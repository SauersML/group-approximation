---
rg: 2
id: leavitt-root-signs-and-clifford-base-corners-cannot-host-the-perfect-synchbcs
kind: claim
title: Leavitt root signs and Clifford base corners cannot host the perfect SynchBCS source
distinct_from:
  orthogonal-steinberg-root-spectral-support-is-not-additive: that gives one exact product-ring representation in which root support is not additive; this turns the example into a characteristic fork, a quantitative orthogonality wall, and a firewall for the Leavitt-corner literature route.
  group-algebra-corners-exclude-traceless-leavitt-inputs: that excludes a traceless Leavitt algebra from every algebraic complex group corner; this also treats a tracial SynchBCS source, explains why coefficient-to-root promotion is not a homomorphism, and fences the locally matricial Clifford base.
  agent-leavitt-not-bcs-negative-root-corner: that is the open direct group-ring-corner target; this proves that neither a coefficient-corner map nor individual root spectral signs can supply that target.
  shared-center-extraspecial-wreath-has-fd-invisible-spin-sector: that constructs an exact finite-dimensional-invisible central sign; this proves that its negative base algebra alone cannot contain the fixed SynchBCS source and forces any surviving map to use actor coefficients.
artifacts:
  - research/leavitt-characteristic-fork-root-overlap-and-clifford-base-proof.md
---

**ESTABLISHED TWO-HOST FIREWALL; NO NONHYPERLINEAR GROUP IS
CLAIMED.**

Let \(\mathcal A_I\) be the finite complex SynchBCS algebra from
`perfect-qc-synchronous-separation-yields-a-finite-bcs-with-no-matrix-model`.
It has a tracial state but no unital finite-dimensional star representation.

## 1. The Leavitt coefficient/root fork

The existing binary-Leavitt Steinberg host is over characteristic two. There
is no unital ring homomorphism from \(\mathcal A_I\), or even from
\(\mathbf C\), into a nonzero corner of a characteristic-two algebra.
Consequently a unital coefficient-corner map

\[
 \mathcal A_I\longrightarrow eL_{\mathbf F_2}(E)e
 \tag{LRC1}
\]

cannot exist.

Changing coefficients to characteristic zero removes that scalar obstruction,
but also removes the marked root sign. For every nonzero coefficient \(a\),

\[
 x_{ij}(a)^m=x_{ij}(ma)\ne 1\qquad(m\geq 1),
 \tag{LRC2}
\]

so \((1-x_{ij}(a))/2\) is not a projection. Thus the characteristic-two
involution and the complex coefficient algebra cannot coexist in this
standard elementary-root realization.

Even if one temporarily stays in characteristic two and applies the
individual root-sign rule

\[
 Q(a)=\frac{1-x_{ij}(a)}2\in\mathbf C[EL_n(R)],
 \tag{LRC3}
\]

the rule does not preserve an orthogonal partition. For
\(R=\mathbf F_2\times\mathbf F_2\), \(e=(1,0)\), and \(f=(0,1)\),

\[
 Q(e+f)=Q(e)+Q(f)-2Q(e)Q(f),\qquad
 \tau\!\left(Q(e)Q(f)\right)=\frac14.
 \tag{LRC4}
\]

Here \(\tau\) is the canonical group trace. In particular
\(\|Q(e)Q(f)\|_2=1/2\). If projections \(P_e,P_f\) satisfy

\[
 \|P_e-Q(e)\|_2\leq\varepsilon_e,\qquad
 \|P_f-Q(f)\|_2\leq\varepsilon_f,
\]

then

\[
 \|P_eP_f\|_2\geq\frac12-\varepsilon_e-\varepsilon_f.
 \tag{LRC5}
\]

Hence small normalized-Hilbert--Schmidt perturbations of the two root signs
cannot become orthogonal. Standard root additivity implements XOR, not the
one-hot/forbidden-overlap relations of \(\mathcal A_I\).

## 2. What the Leavitt-corner theorems do and do not give

Abrams--Nam prove that every nonzero corner of a Leavitt path algebra of a
finite graph is again a Leavitt path algebra. Abrams--Dokuchaev--Nam prove
that every nonzero corner for an arbitrary graph is a Steinberg algebra of an
ample groupoid. In the latter statement "Steinberg algebra" means a groupoid
convolution algebra; it is not the complex group algebra of a Steinberg
group.

These corner theorems do not provide a homomorphism

\[
 eL_K(E)e\longrightarrow q\,\mathbf C[EL_n(L_K(E))]\,q.
 \tag{LRC6}
\]

For complex purely infinite Leavitt corners, no such unital star homomorphism
into a nonzero algebraic complex group-ring corner can exist: the target has
the normalized canonical trace, while a properly infinite unit has no
tracial state. A unital map
\(\mathcal A_I\to eL_{\mathbf C}(E)e\) is not ruled out here; rather, it
cannot be promoted by (LRC3), (LRC6), or the cited corner theorems to the
needed group-ring corner.

## 3. The Kun--Thom Clifford base is also too local

Let \(E(X)\) be the shared-center extraspecial base on an infinite site set,
let \(J\) be its common central involution, and put
\(p_-=(1-J)/2\). Then

\[
 p_-\mathbf C[E(X)]p_-=
 \bigcup_{F\Subset X}p_-\mathbf C[E(F)]p_-,
 \qquad
 p_-\mathbf C[E(F)]p_-\cong M_{2^{|F|}}(\mathbf C).
 \tag{LRC7}
\]

There is no unital star homomorphism

\[
 \mathcal A_I\longrightarrow p_-\mathbf C[E(X)]p_-.
 \tag{LRC8}
\]

Indeed, the images of the finitely many generators have finite group support
and therefore lie together in one matrix algebra in (LRC7), contradicting
the absence of a unital matrix representation.

Thus a map into the full Kun--Thom corner
\(p_-\mathbf C[E(X)\rtimes G]p_-\) must use a nonidentity actor coefficient.
Its normalized canonical corner trace would pull back to a trace on
\(\mathcal A_I\); no injectivity or separate trace-faithfulness hypothesis is
needed. Constructing such a mixed actor occurrence map would already be the
terminal nonhyperlinearity step, and is not supplied here.

## Exact residual gate

The two surviving routes are genuinely mixed.

1. In the binary-Leavitt host, construct finite group-ring projections using
   both nonmonomial coefficient roots and a nonhomogeneous occurrence
   identity which cancels the fixed \(1/4\) overlap in (LRC4).
2. In the shared-center host, construct at least one source generator with
   nontrivial actor support and prove all PVM and forbidden-overlap identities
   in the negative corner.

Coefficient-corner Morita theory, individual root spectral cuts, and the
Clifford base algebra alone cannot close either route.

Primary sources:

- Gene Abrams and T. G. Nam, *Corners of Leavitt path algebras of finite
  graphs are Leavitt path algebras*, main theorem,
  https://arxiv.org/abs/1902.03641
- Gene Abrams, Mikhailo Dokuchaev, and T. G. Nam, *Realizing corners of
  Leavitt path algebras as Steinberg algebras, with corresponding connections
  to graph C-star-algebras*, Theorem 3.6 and Corollary 3.8,
  https://arxiv.org/abs/1909.03964
- Ayten Koc and Murad Ozaydin, *Finite Dimensional Representations of Leavitt
  Path Algebras*, classification theorem,
  https://arxiv.org/abs/1607.04622

DERIVATION
leavitt-characteristic-fork-root-overlap-and-clifford-base-proof
