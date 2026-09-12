# Nonabelian unitary component groups of simple AH algebras

Date: 11 September 2026. Complete argument written by the `lix-sweep` lane.
It has not yet been independently reviewed; no external or formal
verification is claimed.

It extends the LIX toolkit (the gauge/section fibration and the integral
Euler normalization of
[the exact factorial proof](stw59-exact-factorial-component-groups-2026-09-05.md))
from even-cell bases to bases with odd cells. On such a base the component
group acquires a K-theoretic quotient, and a Samelson product turns it into
a nonabelian group.

## 0. Statement

**Theorem 1.** For every integer n>=2 there are a separable, simple,
unital, nuclear, stably finite, infinite-dimensional AH algebra B_n and
unitaries u,v in B_n with the following properties.

1. The canonical map
   \[
   \kappa\colon U(B_n)/U_0(B_n)\to K_1(B_n)
   \]
   is surjective, and its kernel is a central subgroup isomorphic to
   \(\mathbb Z/n!\).
2. The commutator \(uvu^*v^*\) has order exactly n in
   \(U(B_n)/U_0(B_n)\).
3. B_n has a unique tracial state and stable rank exactly two, and
   \(K_1(B_n)\) is free abelian of countably infinite rank.

In particular \(U(B_n)/U_0(B_n)\) is not abelian: uv and vu lie in
different components of \(U(B_n)\), while
\(\operatorname{diag}(uv,1)\) and \(\operatorname{diag}(vu,1)\) lie in one
component of \(U(M_2(B_n))\).

**Context.** Blackadar's classical example of a non-K1-injective algebra
(K-Theory for Operator Algebras, 2nd ed., 8.1.2(d)) is exactly of this shape.
There \(A=C(U(2)\times U(2),M_2)\), and by Araki--James--Thomas the two
coordinate unitaries satisfy: uv and vu are in different components, and
their first stabilizations are in one component. That algebra is not simple.

In the simple classes where K1-injectivity is known (purely infinite,
stable rank one, real rank zero, Z-stable), the component group embeds in
K_1 and so is abelian. Theorem 1 gives simple algebras with the classical
commutator phenomenon. It also refutes STW Problem LIX a second time, now
with a commutator as the witness. No further named problem is claimed.

## 1. A Samelson product of order n

**Proposition 2.** Let n>=2. Let \(\alpha\in\pi_1U(n)\) be the class
of \(z\mapsto\operatorname{diag}(z,1_{n-1})\), and let
\(\omega\in\pi_{2n-1}U(n)\cong\mathbb Z\) be a generator. The Samelson
product \(\langle\alpha,\omega\rangle\in\pi_{2n}U(n)\) has order exactly n.

The only literature facts used are stated in the proof. Bott's general
formula for these products (Comment. Math. Helv. 34 (1960)) is not used.

**Proof.** For based maps \(f:S^1\to U(n)\) and \(g:S^{2n-1}\to U(n)\),
the commutator map
\[
(z,y)\mapsto f(z)g(y)f(z)^{-1}g(y)^{-1}
\]
is 1 on \(S^1\vee S^{2n-1}\). It is therefore the composite of the quotient
\(q:S^1\times S^{2n-1}\to S^1\wedge S^{2n-1}=S^{2n}\) with a based map
\(S^{2n}\to U(n)\). By definition its class is the Samelson product.
Samelson products are bilinear.

Under the adjunction \(\pi_kU(n)\cong\pi_{k+1}BU(n)\), a Samelson product
corresponds, up to sign, to the Whitehead product of the adjoint classes
(H. Samelson, Amer. J. Math. 75 (1953), 744--752; G. W. Whitehead,
Elements of Homotopy Theory, Ch. X). Let \(x_2\in\pi_2BU(n)\) and
\(x_{2n}\in\pi_{2n}BU(n)\) be the adjoints of \(\alpha\) and \(\omega\);
both are generators. By bilinearity it suffices to prove

\[
[x_2,k\,x_{2n}]=0\iff n\mid k .
\tag{1.1}
\]

The product \(S^2\times S^{2n}\) is \(S^2\vee S^{2n}\) with one cell
attached along the universal Whitehead product. So a map
\(S^2\vee S^{2n}\to BU(n)\) with components \((y,z)\) extends over the
product exactly when \([y,z]=0\). Since \(BU(n)\) is simply connected,
extensions correspond to rank-n complex bundles on \(S^2\times S^{2n}\)
with prescribed restrictions to the two spheres.

*Bundles on the spheres.* A rank-n bundle on \(S^2\) is determined by its
first Chern class, and \(x_2\) has \(c_1=\pm a\), where a generates
\(H^2(S^2;\mathbb Z)\).

A rank-n bundle on \(S^{2n}\) is determined by its class in
\(\widetilde K^0(S^{2n})\cong\mathbb Z\), because \(U/U(n)\) is
2n-connected, so \(\pi_{2n}BU(n)\to\pi_{2n}BU\) is an isomorphism. For any
complex bundle, \(\log c=\sum_{q\ge1}(-1)^{q-1}(q-1)!\,\mathrm{ch}_q\) as
power series in the Chern roots. On \(S^{2n}\) only \(c_n\) can be nonzero,
so \(c_n=(-1)^{n-1}(n-1)!\,\mathrm{ch}_n\).

The Bott generator has \(\mathrm{ch}_n\) equal to an integral generator b of
\(H^{2n}(S^{2n};\mathbb Z)\) (Hatcher, *Vector Bundles and K-Theory*,
Prop. 4.3). Hence \(k\,x_{2n}\) has \(c_n=\pm k(n-1)!\,b\).

*Necessity in (1.1).* Let E be a rank-n bundle on \(S^2\times S^{2n}\)
restricting to \(x_2\) and to \(k\,x_{2n}\). Write a, b also for the
pullbacks of the generators.

The integral cohomology is free on 1, a, b, ab, and \(H^{2j}=0\) unless
\(j\in\{0,1,n,n+1\}\); these degrees are distinct because n>=2. So
\[
c(E)=1+\epsilon a+\sigma k(n-1)!\,b,\qquad \epsilon,\sigma=\pm1 .
\]
There is no degree-(2n+2) term, since \(c_{n+1}\) vanishes in rank n.
Because \(a^2=b^2=0\),
\[
\log c(E)=\epsilon a+\sigma k(n-1)!\,b-\epsilon\sigma k(n-1)!\,ab .
\]
Comparing the degree-(2n+2) parts gives
\((-1)^nn!\,\mathrm{ch}_{n+1}(E)=-\epsilon\sigma k(n-1)!\,ab\), that is
\[
\mathrm{ch}_{n+1}(E)=\pm\frac kn\,ab .
\]

The Chern character of every bundle on \(S^2\times S^{2n}\) is integral.
Indeed \(\Sigma(S^2\times S^{2n})\simeq\Sigma(S^2\vee S^{2n}\vee S^{2n+2})\),
so \(\widetilde K^0(S^2\times S^{2n})\) is the sum of the reduced K-groups
of three spheres, each generated by a class with integral Chern character.
Therefore n divides k.

*Sufficiency for k=n.* Let \(\ell\) be the pullback of a line bundle on
\(S^2\) with \(c_1(\ell)=a\). Let \(\eta\) be the pullback of the rank-zero
class \(n\kappa_{2n}\) on \(S^{2n}\), with the sign of the Bott class
\(\kappa_{2n}\) chosen so that \(c(\eta)=1+n!\,b\). Let \(\gamma\) be the
pullback, along the collapse \(S^2\times S^{2n}\to S^{2n+2}\), of the
rank-zero class with \(\mathrm{ch}=ab\); then
\(c(\gamma)=1+(-1)^nn!\,ab\). For \(s\in\mathbb Z\) put
\(\xi=(\ell-1)+\eta+s\gamma\). By the Whitney formula,
\[
c(n+\xi)=(1+a)(1+n!\,b)\bigl(1+s(-1)^nn!\,ab\bigr)
=1+a+n!\,b+\bigl(1+s(-1)^n\bigr)n!\,ab .
\]
Take \(s=-(-1)^n\). Then \(c_{n+1}(n+\xi)=0\).

Next, realize this class by an honest rank-n bundle.
- After adding a trivial bundle, \(n+\xi\) is an actual bundle of large rank.
- A bundle of rank at least n+2 on the (2n+2)-dimensional complex splits
  off a trivial line, because its sphere fibre has dimension at least 2n+3.
  So the class is represented by a bundle V of rank n+1.
- The only obstruction to a nowhere-zero section of V lies in
  \(H^{2n+2}(S^2\times S^{2n};\pi_{2n+1}S^{2n+1})\) and is the Euler class
  \(c_{n+1}(V)=0\). Hence \(V\cong E\oplus\mathbf 1\) with E of rank n and
  \(c(E)=c(n+\xi)\).

Restrictions of E: \(\gamma\) restricts trivially to both spheres, and
\(\eta\) restricts trivially to \(S^2\). So \(E|_{S^2}\) has stable class
\(n+(\ell-1)\), hence \(E|_{S^2}=\pm x_2\). Also \(E|_{S^{2n}}\) has stable
class \(n+\eta\), hence \(E|_{S^{2n}}=\pm n\,x_{2n}\). The corresponding map
extends, so \(n[x_2,x_{2n}]=0\) by bilinearity. This proves (1.1), and so
\(\langle\alpha,\omega\rangle\) has order exactly n. \(\square\)

## 2. Finite stages over S^1 x S^(2n-1) x Y

Keep the notation of the exact factorial proof, Section 1:
- \(Y=\prod_{j\le\ell}\mathbb{CP}^{d_j}\), possibly empty, with
  \(m=\sum_jd_j\) and \(H=\bigoplus_jL_j^{\oplus d_j}\);
- now \(X=S^1\times S^{2n-1}\times Y\), \(E=\mathbf 1^n\oplus H\) and
  \(r=n+m\), so that \(\operatorname{rank}E=r\) and \(\dim X=2r\);
- \(\mathcal G(E)=U(\Gamma(X,\operatorname{End}E))\),
  \(F=E\oplus\mathbf 1\), and \(\mathcal S(F)\) is the space of unit
  sections of F;
- \(Q=q\times\mathrm{id}_Y:X\to S^{2n}\times Y\) is the degree-one collapse.

**Theorem 3.**

(a) There is an exact sequence of groups
\[
1\to\mathbb Z/n!\xrightarrow{\ \partial\ }\pi_0\mathcal G(E)
\xrightarrow{\ \kappa\ }K^1(X)\to 1 ,
\]
where \(\kappa\) is the canonical map into
\(K_1(\Gamma(\operatorname{End}E))\cong K^1(X)\), and the image of
\(\partial\) is central.

(b) \(Q^*\) maps \(\pi_0\mathcal G(\mathbf 1^n\oplus H\text{ over }S^{2n}\times Y)\cong\mathbb Z/n!\)
isomorphically onto \(\partial(\mathbb Z/n!)\).

(c) Put \(u=(\alpha\circ\mathrm{pr}_{S^1})\oplus1_H\) and
\(v=(\omega\circ\mathrm{pr}_{S^{2n-1}})\oplus1_H\), using based
representatives. Their commutator lies in \(\partial(\mathbb Z/n!)\) and has
order exactly n in \(\pi_0\mathcal G(E)\). In particular
\(\pi_0\mathcal G(E)\) is not abelian.

(d) Let e>=1, \(X'=X\times\mathbb{CP}^e\) and
\(E'=\mathrm{pr}^*E\oplus L^{\oplus e}\), and let
\(T(g)=\mathrm{pr}^*g\oplus1\). Then T is injective on \(\pi_0\), it is an
isomorphism on the kernels in (a), and \(\kappa\circ T=\mathrm{pr}^*\circ\kappa\).

**Proof of (a).** Lemma 2 of the factorial proof (the locally trivial
principal bundle \(\mathcal G(E)\to\mathcal G(F)\to\mathcal S(F)\), with
\(\pi_0\mathcal S(F)=0\) and \(\pi_1\mathcal S(F)\cong H^{2r}(X;\mathbb Z)\))
uses only \(\dim X=2r\) and \(H^{2r}(X;\mathbb Z)\cong\mathbb Z\). Both hold.

Lemma 3 there identifies \(\pi_0\mathcal G(F)\cong K^1(X)\) and
\(\pi_1\mathcal G(F)\cong K^0(X)\) through canonical stabilization. That
argument holds for every finite CW complex of dimension 2r; even cells were
used only to conclude \(K^1(X)=0\). Here
\[
K^1(X)\cong K^1(S^1\times S^{2n-1})\otimes K^0(Y)\cong\mathbb Z^2\otimes K^0(Y)\ne0 .
\]
The homotopy sequence of the principal bundle, together with
\(\pi_0\mathcal S(F)=0\), gives the exact sequence
\[
K^0(X)\xrightarrow{\ \epsilon_*\ }\mathbb Z\xrightarrow{\ \partial\ }
\pi_0\mathcal G(E)\to\pi_0\mathcal G(F)=K^1(X)\to0 .
\]
The last map is \(\kappa\), since both identifications are the canonical
stabilizations.

*Image of \(\epsilon_*\).* Formula (4.5) of the factorial proof holds
verbatim. It needs only the Künneth splitting
\(K^0(S^2\times X)=K^0(X)\oplus b\,K^0(X)\) and torsion-free cohomology of
\(S^2\times X\), and both hold here.

For its Section 5 the only change is the top class on the sphere factor.
Because \(K^1(Y)=0\) and \(K^*(Y)\) is free,
\(K^0(X)=K^0(S^1\times S^{2n-1})\otimes K^0(Y)\). Since
\(\Sigma(S^1\times S^{2n-1})\simeq S^2\vee S^{2n}\vee S^{2n+1}\),
\(\widetilde K^0(S^1\times S^{2n-1})\cong\mathbb Z\). The class
\(\kappa'=q^*\kappa\) generates it: its Chern character \(q^*x\) is an
integral generator of \(H^{2n}\), because q has degree one. So
\(K^0(X)=K^0(Y)\oplus\kappa'K^0(Y)\), exactly as in (5.1).

Every other factor of (4.5) is pulled back from Y. The computation
(5.2)--(5.6) goes through with \(\kappa'\) in place of \(\kappa\), and gives
\(\operatorname{im}\epsilon_*=n!\,\mathbb Z\).

*Centrality.* Let \(k\in\mathcal G(E)\), and let \(\gamma\) be a based loop
in \(\mathcal S(F)\). Lift it to a path \(g_t\) in \(\mathcal G(F)\) with
\(g_0=1\), so that \(g_1\in\mathcal G(E)\) represents \(\partial[\gamma]\).
Since \(ke=e\), the path \(kg_tk^{-1}\) lifts the loop \(k\gamma\). So
conjugation by k sends \(\partial[\gamma]\) to \(\partial[k\gamma]\).

The integer of a loop is its relative Euler number over \(D^2\times X\)
(Section 4 of the factorial proof). The complex bundle automorphism k fixes
e and carries a transverse extension to a transverse extension with the same
local indices. So \([k\gamma]=[\gamma]\), and \(\partial(\mathbb Z/n!)\) is
central. \(\square\)

**Proof of (b).** Pulling sections and gauge transformations back along Q
maps the principal-bundle sequence over \(S^{2n}\times Y\) to the one over
X. On \(\pi_1\mathcal S\), Q induces the isomorphism
\(H^{2r}(S^{2n}\times Y;\mathbb Z)\to H^{2r}(X;\mathbb Z)\), since Q has
degree one and obstruction classes are natural. Both images of
\(\epsilon_*\) are \(n!\,\mathbb Z\): the factorial proof's Theorem 1 over
\(S^{2n}\times Y\), and (a) over X. So the induced map on cokernels is an
isomorphism. By that Theorem 1, the group over \(S^{2n}\times Y\) is this
cokernel. \(\square\)

**Proof of (c).** Pointwise, \(uvu^*v^*\) is the commutator map of
\(\alpha,\omega\) in the \(S^1\times S^{2n-1}\) coordinates, direct sum
\(1_H\). By Section 1 it equals
\(Q^*\bigl((\langle\alpha,\omega\rangle\circ\mathrm{pr}_{S^{2n}})\oplus1_H\bigr)\).

For \(Y=\mathrm{pt}\), part (b) says that \(q^*\) is injective on
\(\pi_{2n}U(n)=\pi_0\mathcal G(\mathbf 1^n\text{ over }S^{2n})\). The
passage from \(Y=\mathrm{pt}\) to general Y is a composite of the maps T of
(d), one projective factor at a time; these are isomorphisms on kernels.
Hence the class of \(uvu^*v^*\) has the order of
\(\langle\alpha,\omega\rangle\), which is n by Proposition 2. \(\square\)

**Proof of (d).** Extension by the identity maps the principal-bundle
sequence of E to that of E', sending a section loop s to \(s\oplus0\). As in
Section 5 of
[the finite-abelian proof](stw59-exact-finite-abelian-component-groups-2026-09-05.md),
a signed count of product zeros multiplies the integer by
\(\langle c_e(L^{\oplus e}),[\mathbb{CP}^e]\rangle=\pm1\). Both images of
\(\epsilon_*\) are \(n!\,\mathbb Z\) by (a), so T is an isomorphism on
kernels.

On quotients, \(\kappa(T g)=[\mathrm{pr}^*g\oplus1]=\mathrm{pr}^*\kappa(g)\),
which is injective because pr has a section.

Injectivity of T: if \(Tg=1\), then \(\mathrm{pr}^*\kappa(g)=0\), so
\(\kappa(g)=0\) and \(g=\partial(t)\). Then \(\partial'(\pm t)=Tg=1\), so
t=0 and g=1. \(\square\)

## 3. The simple limit

Fix n>=2 and define the system:
- \(r_i=n2^i\), \(Y_i=\prod_{j<i}\mathbb{CP}^{r_j}\),
  \(X_i=S^1\times S^{2n-1}\times Y_i\);
- \(E_i=\mathbf 1^n\oplus\bigoplus_{j<i}L_{j+1}^{\oplus r_j}\) and
  \(A_i=\Gamma(X_i,\operatorname{End}E_i)\), so that
  \(\operatorname{rank}E_i=r_i\) and \(\dim X_i=2r_i\);
- evaluation points \(x_i\in X_i\) with dense projected tails. For example,
  list each member of a countable dense subset of
  \(S^1\times S^{2n-1}\times\prod_{j\ge0}\mathbb{CP}^{r_j}\) infinitely
  often and project its i-th term.

After identifying \(E_i(x_i)\) with \(\mathbb C^{r_i}\), put
\[
\varphi_i(a)=\pi_i^*a\oplus\bigl(a(x_i)\otimes1_{L_{i+1}}\bigr),
\qquad B_n=\varinjlim(A_i,\varphi_i),
\]
so that \(E_{i+1}=\pi_i^*E_i\oplus L_{i+1}^{\oplus r_i}\).

**Proof of Theorem 1.**

*Structure.* The base factor \(S^1\times S^{2n-1}\) replaces \(S^{2n}\), and
nothing in the following arguments depends on that factor:
- simplicity from the dense tails, and separability, unitality, nuclearity,
  the AH form and infinite dimensionality: Section 7 of the finite-abelian
  proof, verbatim;
- stable finiteness, from a compatible family of traces;
- a unique trace: Section 2 of
  [the unique-trace proof](stw59-unique-trace-and-matrix-stability-2026-09-05.md).
  It uses only that the two blocks of \(\varphi_i\) have equal rank and that
  every \(X_i\) is connected.

*Component group.* The map induced by \(\varphi_i\) on \(\pi_0\) is the map
T of Theorem 3(d) with \(e=r_i\). The evaluation block contracts: a path in
\(U(r_i)\) from \(g(x_i)\) to 1, tensored with \(1_{L_{i+1}}\), joins
\(\varphi_i(g)\) to \(\pi_i^*g\oplus1\).

The component group of the unital injective limit is the direct limit of the
stage component groups (proof of Corollary 4 of the factorial proof:
polar-unitary approximation for surjectivity, finite-stage path detection
for injectivity).

On K-theory, \(K_1(B_n)=\varinjlim K^1(X_i)\). The connecting maps are
\(\pi_i^*\), because the evaluation block factors through \(M_{r_i}(\mathbb C)\),
whose \(K_1\) vanishes. So \(\kappa\) is compatible with the limit.

A direct limit of exact sequences of groups is exact. The kernel maps are
isomorphisms \(\mathbb Z/n!\to\mathbb Z/n!\), and a limit of central
subgroups is central. This proves item 1.

*Commutator.* u and v live at stage 0, where \(Y_0\) is a point. By Theorem
3(c) their commutator has order n there. Every connecting map is injective
on \(\pi_0\) by Theorem 3(d), and a class trivial in the limit is trivial at
some stage. So the order is n in the limit: item 2.

*Stable rank, trace, K_1.* Nistor's Theorem 7(a) (J. Operator Theory 17
(1987)) gives \(\operatorname{sr}(A_i)=2\) for a homogeneous algebra of
degree \(r_i\) over a base of dimension \(2r_i\). Approximation passes the
bound \(\operatorname{sr}(B_n)\le2\) to the limit (unique-trace proof,
Section 5). Stable rank one would make \(\kappa\) injective (Rieffel), but
\(uvu^*v^*\) is a nontrivial element of its kernel. Hence
\(\operatorname{sr}(B_n)=2\).

Each \(K^1(X_i)\cong\mathbb Z^2\otimes K^0(Y_i)\) is free of finite rank
tending to infinity. The connecting maps \(\pi_i^*\) are split injective, so
the limit is free abelian of countably infinite rank. This proves item 3.

*Corollary.* \(uvu^*v^*\notin U_0(B_n)\), so \(uv\) and \(vu\) lie in
different components. Rotating a two-by-two block gives
\(\operatorname{diag}(uv,1)\sim\operatorname{diag}(u,v)\sim\operatorname{diag}(vu,1)\)
in \(U(M_2(B_n))\). \(\square\)

## 4. Scope and next steps

- *Why the kernel is central.* In the regime \(\dim X=2\operatorname{rank}E\)
  there is exactly one unstable obstruction, a top-cell integer, and
  conjugation preserves it. So every tower of this kind yields a central
  extension of \(K_1\) by a cyclic group, a group of nilpotency class at most
  two. Class three or more would need bases of dimension beyond twice the
  rank, where several obstructions interact.
- *Other commutator orders.* Replacing \(S^1\times S^{2n-1}\) by
  \(S^{2i-1}\times S^{2j-1}\) with i+j=n+1 should give commutators of order
  \(n\binom{n-1}{i-1}\), by Bott's (i-1)!(j-1)! formula. This is not proved
  here.
- *Several commutator pairs.* The joined-arm construction of the
  finite-abelian proof, with arms \(S^1\times S^{2n_\alpha-1}\), is the
  natural route to several independent commutator pairs.
- *Named problems.* The general realization question (which groups occur as
  \(U(A)/U_0(A)\) for simple unital A) stays open beyond these central
  extensions. No named problem other than the second refutation of LIX is
  claimed.

## References

1. [Exact factorial component groups](stw59-exact-factorial-component-groups-2026-09-05.md), Sections 1--6.
2. [Finite abelian component groups](stw59-exact-finite-abelian-component-groups-2026-09-05.md), Sections 5 and 7.
3. [Unique trace and matrix stability](stw59-unique-trace-and-matrix-stability-2026-09-05.md), Sections 2 and 5.
4. B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge 1998, 8.1.2(d) and §8.1.
5. S. Araki, I. M. James, E. Thomas, Homotopy-abelian Lie groups, *Bull. Amer. Math. Soc.* 66 (1960), 324--326.
6. H. Samelson, A connection between the Whitehead and the Pontryagin product, *Amer. J. Math.* 75 (1953), 744--752.
7. G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer 1978, Ch. X.
8. A. Hatcher, *Vector Bundles and K-Theory*, Prop. 4.3 and §3.3; [author's text](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf).
9. V. Nistor, Stable rank for a certain class of type I C*-algebras, *J. Operator Theory* 17 (1987), 365--373, Theorem 7(a).
