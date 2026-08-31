---
rg: 2
id: elementary-root-retraction-and-linear-soficity-firewall-proof
kind: route
title: Separate elementary syntactic faithfulness from unitary trace transport
target: steinberg-unitization-encodes-hecke-sums-but-is-trace-blind
requires:
  - unique-central-block-realizes-hecke-predicates-but-forces-affine-group-spectra
  - split-steinberg-conditional-swap-has-root-kernel-countermodel
  - amenable-edge-cycles-cannot-create-an-lcs-gap
---

# Separate elementary syntactic faithfulness from unitary trace transport

## 1. Elementary matrices faithfully encode a finite coefficient table

Let \(A\) be a unital ring.  Since \(E_{ij}^2=0\) for \(i\neq j\),

\[
 x_{ij}(a)^{-1}=x_{ij}(-a)
\tag{1}
\]

and direct multiplication gives

\[
 x_{ij}(a)x_{ij}(b)=x_{ij}(a+b).
\tag{2}
\]

For distinct \(i,j,k\), the only nonzero cross term is
\(E_{ij}E_{jk}=E_{ik}\), whence

\[
 [x_{ij}(a),x_{jk}(b)]=x_{ik}(ab).
\tag{3}
\]

Finally, inspection of the \((i,j)\)-entry gives

\[
 x_{ij}(a)=x_{ij}(b)\quad\Longleftrightarrow\quad a=b.
\tag{4}
\]

Thus, inside the actual elementary matrix group, a named finite coefficient
table has a faithful wordization: addition is (2), multiplication is (3),
and equality is (4).  A finite presentation may name the finitely many
coefficients and impose the finitely many instances needed by a finite BCS
menu.  This is a statement about the syntactic table.  It says nothing yet
about traces on representations of the resulting abstract group.

For a projection \(p=p^*=p^2\), multiply the three matrices in

\[
 W_p=x_{12}(p)x_{21}(-p)x_{12}(p)
\tag{5}
\]

to obtain

\[
 W_p=
 \begin{pmatrix}
 1-p&p\\
 -p&1-p
 \end{pmatrix}.
\tag{6}
\]

Using \(p(1-p)=0\), one checks

\[
 W_p^*W_p=I,\qquad
 W_p^2=
 \begin{pmatrix}
 1-2p&0\\
 0&1-2p
 \end{pmatrix}.
\tag{7}
\]

This proves the exact Whitehead unitization assertion.

## 2. A coefficient star representation does not unitarize the roots

Let \(\pi:A\to M\) be a unital star homomorphism into a complex finite von
Neumann algebra and suppose \(P=\pi(p)\neq0\).  On \(M_2(M)\), put

\[
 U=I+PE_{12}.
\tag{8}
\]

Then

\[
 U^*U
 =I+PE_{12}+PE_{21}+PE_{22}.
\tag{9}
\]

In particular its \((1,2)\)-entry is \(P\neq0\), so \(U\) is not unitary.
The assignment

\[
 x_{12}(p)\longmapsto I+\pi(p)E_{12}
\tag{10}
\]

therefore does not define a unitary group representation.  The same
observation applies to every nonzero self-adjoint coefficient.

The composite \(W_p\) in (6) is unitary under \(\pi\), but the factorization
(5) does not become a factorization by unitaries.  Treating \(W_p\) as a new
abstract involutive generator retains (7) only as a relation among selected
unitaries; the elementary addition and multiplication calculus no longer
comes from the coefficient trace automatically.

There is no characteristic-\(\ell\) shortcut.  In characteristic \(\ell\),

\[
 x_{ij}(a)^\ell=x_{ij}(\ell a)=1,
\tag{11}
\]

so an abstract unitary image of a root is possible.  But if \(A\) has
characteristic \(\ell\) and \(M\neq0\) is a complex unital star algebra, a
unital ring homomorphism would give

\[
 0=\pi(\ell1_A)=\ell1_M,
\tag{12}
\]

a contradiction.  Thus the finite-order root model and the chosen complex
non-CE coefficient trace cannot be the same representation.

## 3. Every homogeneous root attachment retracts

Let \(K_{\rm ext}=\langle S\mid R_{\rm ext}\rangle\) be the external context
group.  Consider a presentation

\[
 \Gamma=\langle S,X\mid R_{\rm ext},R_{\rm root},R_{\rm mix}\rangle,
\tag{13}
\]

where \(X\) is the finite list of named elementary-root generators.  Assume
that every relator in \(R_{\rm root}\cup R_{\rm mix}\) becomes the identity
after every letter from \(X\) is set equal to \(1\).  Then

\[
 \varepsilon:\Gamma\longrightarrow K_{\rm ext},
 \qquad
 \varepsilon(s)=s,\quad\varepsilon(x)=1
\tag{14}
\]

is a well-defined retraction of the evident inclusion of the external
presentation.

Every standard elementary-table relation has this homogeneity:

- both sides of root addition die;
- every Steinberg multiplication commutator dies;
- Weyl transport and external covariance send one dying root to another;
- an equality of two named roots becomes \(1=1\);
- every Whitehead word assembled only from roots dies.

Therefore a split attachment of the finite Heisenberg Hecke tables has
(14).  If \(\sigma\) is any unitary representation of \(K_{\rm ext}\), then

\[
 \sigma\circ\varepsilon
\tag{15}
\]

is an exact unitary representation of \(\Gamma\) in which every coefficient
test is trivial.  Any forbidden external selector sector, or any external
central phase retained by \(\sigma\), survives unchanged.

This is stronger than a failure of a quantitative estimate: the proposed
root tests have an exact zero-defect countermodel.  To avoid it, at least
one relation must remain nontrivial after the root letters are killed.  Such
a relation must also be verified in the intended non-CE trace
representation; Section 2 shows that the raw coefficient-root model cannot
perform that verification.

## 4. The finite-coefficient matrix group is residually finite

Let \(K\) be finite and let \(\mathcal O\) be a finitely generated subring
of a number field \(F\).  Left multiplication on the free
\(\mathcal O\)-module with basis \(K\) is faithful, giving

\[
 \mathcal O[K]\hookrightarrow
 \operatorname{End}_{\mathcal O}(\mathcal O[K])
 \cong M_{|K|}(\mathcal O).
\tag{16}
\]

Entrywise application gives

\[
 \operatorname{GL}_n(\mathcal O[K])
 \hookrightarrow \operatorname{GL}_{n|K|}(F).
\tag{17}
\]

Let \(\Gamma_{\rm loc}\) be any finitely generated subgroup of the left
side.  It is a finitely generated linear group in characteristic zero.
Malcev residual finiteness therefore gives

\[
 \Gamma_{\rm loc}\ \text{is residually finite}.
\tag{18}
\]

For the particular signed Hecke menus, all coefficients lie in a ring of
the form

\[
 \mathbf Z[\zeta_D,1/D]
\tag{19}
\]

after one common denominator and one cyclotomic splitting field are chosen,
so (16)--(18) apply.

Residual finiteness implies soficity and hyperlinearity.  Hence every
canonical group von Neumann algebra \(L(\Gamma_{\rm loc})\), every
finite-subgroup central block in it, and every von Neumann subalgebra of
such a positive corner is Connes embeddable.

Suppose a BCS star algebra \(\mathcal B\) with no Connes-embeddable tracial
state admitted a unital star homomorphism

\[
 \Phi:\mathcal B\longrightarrow
 pL(\Gamma_{\rm loc})p
\tag{20}
\]

for a nonzero finite-subgroup block projection \(p\).  The normalized
canonical corner trace composed with \(\Phi\) would be a Connes-embeddable
tracial state on \(\mathcal B\), contradicting the choice of \(\mathcal B\).
Thus (20) cannot exist.

The same firewall persists under the already established hyperlinear
permanence for finite graphs of hyperlinear vertex groups with amenable edge
groups.  In particular, coupling finitely many local linear unitizations by
finite Heisenberg or cyclic overlap subgroups cannot create the required
canonical non-CE corner.

## 5. Exact residual gate

The elementary functor solves the algebraic word problem posed by the Hecke
sums, and the Whitehead word makes each individual projection reflection
unitary.  The two facts do not combine into trace transport:

\[
 \text{faithful coefficient roots}
 \quad\not\Longrightarrow\quad
 \text{unitary representation of the coefficient trace}.
\tag{21}
\]

A viable compiler must simultaneously prove:

1. a load-bearing mixed relation destroys the retraction (14);
2. the selected non-CE trace extends to a unitary representation satisfying
   that relation;
3. in arbitrary matrix microstates, nontriviality of the protected group
   mark forces a nonzero common root coefficient quotient; and
4. the canonical group trace on the resulting corner pulls back to the
   source trace face.

Items 3--4 are precisely the root-kernel reflection problem, not another
finite-table identity.  Without them, Steinberg unitization either stays in
the residually finite local matrix group (17) or admits the exact root-kernel
countermodel (15).
