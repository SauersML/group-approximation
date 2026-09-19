# Factorial torsion in the unitary components of simple AH algebras

Date: 5 September 2026. Complete proof; independent internal review completed.
This strengthens the order-two construction in the
[LIX manuscript](stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md).
It does not claim a second named open-problem solution or external verification.
The [independent review](stw59-factorial-torsion-independent-review-2026-09-05.md)
checks the full manuscript and exact-order assertions.

## The theorem

**Theorem.** For every integer \(n\ge2\), there are a separable, simple,
unital, nuclear, stably finite AH algebra \(A^{(n)}\) and a unitary
\(v_n\in U(A^{(n)})\) such that
\[
K_1(A^{(n)})=0,\qquad
\operatorname{ord}([v_n]\in U(A^{(n)})/U_0(A^{(n)}))=n!.
\tag{1}
\]
Moreover \(\operatorname{diag}(v_n,1)\) is null-homotopic in
\(U(M_2(A^{(n)}))\).

Consequently, for every finite integer \(d\ge2\), a simple unital
nuclear stably finite AH algebra with zero \(K_1\) has a unitary
component of order exactly \(d\). These assertions concern cyclic
subgroups, not the whole unitary component group. The algebra may
depend on \(d\).

The argument replaces parity by divisibility by \(n!\). It then tests
every power of the initial unitary by the degree of a sphere map.

## 1. The finite factorial obstruction

Fix positive integers \(d_1,\ldots,d_\ell\), allowing the empty list, and put
\[
Y=\prod_{j=1}^{\ell}\mathbb{CP}^{d_j},\qquad
m=\sum_jd_j,\qquad H=\bigoplus_j L_j^{\oplus d_j}.
\]
Here \(L_j\) is the tautological line from the indicated factor.
With \(h_j=c_1(L_j)\),
\[
H^*(Y;\mathbb Z)=\mathbb Z[h_1,\ldots,h_\ell]/(h_j^{d_j+1}),
\qquad
\left|\langle c_m(H),[Y]\rangle\right|=1.
\tag{2}
\]
The cohomology is torsion-free, \(K^1(Y)=0\), and \(K^0(Y)\) is free
abelian and generated additively by line monomials \(\prod_jL_j^{a_j}\).
These are the usual projective-space computations in complex K-theory.

Let
\[
M=S^{2n+1}\times Y,\quad V=\mathbf1^{n+1}\oplus H,
\quad r=n+1+m.
\]

**Lemma 1.** If a rank-\(r\) complex bundle \(W\) on \(S^1\times M\)
restricts to \(V\) on a slice \(\{1\}\times M\), then
\[
\langle c_r(W),[S^1\times M]\rangle\in n!\mathbb Z.
\tag{3}
\]

**Proof.** Write \(p:S^1\times M\to M\) for projection and
\(\delta=[W]-[p^*V]\). The split restriction sequence and the
torsion-free Künneth theorem give
\[
\ker(K^0(S^1\times M)\to K^0(M))
=K^1(S^1)\otimes K^1(S^{2n+1})\otimes K^0(Y).
\]
Choose integral generators \(t\in H^1(S^1;\mathbb Z)\) and
\(x\in H^{2n+1}(S^{2n+1};\mathbb Z)\), and put \(z=tx\).
The odd Bott generator has Chern character \(x\), with coefficient
one: it is the suspension of the generator on \(S^{2n+2}\) whose
top Chern character is an integral generator. Therefore
\[
\operatorname{ch}(\delta)=z\operatorname{ch}(\beta)
\quad\text{for some }\beta\in K^0(Y).
\tag{4}
\]
All products of positive-degree terms in (4) vanish, since \(z^2=0\).
The identity
\(\log c(\delta)=\sum_{q\ge1}(-1)^{q-1}(q-1)!\operatorname{ch}_q(\delta)\)
thus gives
\[
c_q(\delta)=(-1)^{q-1}(q-1)!\operatorname{ch}_q(\delta).
\tag{5}
\]
For a line monomial \(\beta=\prod_jL_j^{a_j}\), a coefficient of
\(z\prod_jh_j^{b_j}\), with \(|b|=q-n-1\), in (5) is
\[
(-1)^{q-1}\frac{(|b|+n)!}{\prod_jb_j!}\prod_ja_j^{b_j}
=(-1)^{q-1}n!\binom{|b|+n}{n}
\binom{|b|}{b_1,\ldots,b_\ell}\prod_ja_j^{b_j}.
\tag{6}
\]
It is divisible by \(n!\); there are no terms when \(q<n+1\).
Linearity in \(\beta\) proves the same for every positive Chern
class of \(\delta\). Torsion-free integral cohomology makes this an
integral assertion, not merely a rational calculation.

Finally \(c(W)=c(p^*V)c(\delta)\). Since \(V\) is pulled back
from the \(2m\)-dimensional space \(Y\), \(c_r(V)=0\).
Every remaining term of \(c_r(W)\) contains a positive Chern class
of \(\delta\), hence is divisible by \(n!\). This proves (3). \(\square\)

Let \(F_n\to S^{2n+1}\subset\mathbb C^{n+1}\) be the rank-\(n\)
bundle with fiber \((F_n)_x=x^\perp\). For a smooth map
\(f:S^{2n+1}\to S^{2n+1}\) of degree \(k\), put \(F_{n,k}=f^*F_n\).

**Lemma 2.** If \(n!\nmid k\), then
\[
F_{n,k}\oplus H\not\cong\mathbf1^n\oplus H
\quad\text{on }S^{2n+1}\times Y.
\tag{7}
\]

**Proof.** Choose a unit vector \(e\in\mathbb C^{n+1}\) such that
\(-e\) is a regular value of \(f\). The bundle \(V\) has unit
sections \((e,0)\) and \((f(x),0)\). An isomorphism of their
orthogonal complements would extend, by polar decomposition and
\(e\mapsto f(x)\), to a unitary bundle automorphism \(g\) of \(V\).
Form its mapping torus using the convention
\((v,1)\sim(g^{-1}v,0)\).

Choose a transverse smooth section \(\sigma\) of \(H\) and a
function \(\chi\) vanishing near the endpoints of \([0,1]\) and
equal to one near \(1/2\). The section
\[
S(x,y,t)=((1-t)e+t f(x),\chi(t)\sigma(y))
\tag{8}
\]
descends to the mapping torus. Its zeros are precisely
\(t=1/2\), \(f(x)=-e\), \(\sigma(y)=0\).
At each such point the derivative of the first component is
\[
(\xi,a)\longmapsto\tfrac12 df_x(\xi)-2ae.
\]
It is an isomorphism of real vector spaces. Its local orientation
sign is a fixed sign, independent of \(x\), times the local degree
of \(f\) at \(x\). The signed zero count of (8) is therefore
\[
\pm\deg(f)\langle c_m(H),[Y]\rangle=\pm k.
\tag{9}
\]
The section is nonvanishing near the gluing seam, so a continuous
\(g\) causes no problem: the Euler number is the sum of the displayed
local indices, or one may smooth away from their neighborhoods.
The Euler class of a complex bundle is its top Chern class. Equation
(9) contradicts Lemma 1 if \(n!\nmid k\). \(\square\)

## 2. Detecting every power of the unitary

The fibration
\[
U(n)\longrightarrow U(n+1)\longrightarrow S^{2n+1}
\]
has boundary homomorphism
\(\partial:\pi_{2n+1}(S^{2n+1})\to\pi_{2n}(U(n))\).
Bott's unstable computation gives
\[
\pi_{2n}(U(n))\cong\mathbb Z/n!,\qquad
\pi_{2n}(U(n+1))=0.
\tag{10}
\]
The boundary of the sphere generator is thus a generator. Fix a
based representative \(u_n:S^{2n}\to U(n)\) of it, with the
clutching convention making its bundle \(F_n\).

For every integer \(k\), pointwise multiplication \(u_n^k\)
represents \(k\partial(1)=\partial(k)\): the group operation on
homotopy groups of a topological group agrees with pointwise
multiplication. Naturality of the boundary and of bundle pullback
identifies its clutched bundle with \(F_{n,k}\). Thus this step
uses the degree \(k\) of a map on \(S^{2n+1}\), not a purported
degree of a map into \(U(n)\).

On \(X=S^{2n}\times Y\), let \(E=\mathbf1^n\oplus H\) and
\(w=u_n\oplus1_H\in U(\Gamma(\operatorname{End}E))\).
If \(w^k\) were null-homotopic, its homotopy would extend the
clutching automorphism over a hemisphere. This would identify
\(F_{n,k}\oplus H\) with \(\mathbf1^n\oplus H\), contradicting
Lemma 2 whenever \(n!\nmid k\). Conversely \(u_n^{n!}\) is
null-homotopic by (10), so \(w^{n!}\) is null-homotopic.
We have proved the exact equivalence
\[
w^k\in U_0(\Gamma(\operatorname{End}E))\quad\Longleftrightarrow\quad n!\mid k.
\tag{11}
\]
Also \(u_n\oplus1\) contracts in \(U(n+1)\) by (10).
One trivial line in a second copy of \(E\) supplies this contraction
for \(\operatorname{diag}(w,1_E)\).

## 3. A simple inductive limit preserving the whole cyclic subgroup

Set
\[
r_i=n2^i,\quad Y_i=\prod_{j<i}\mathbb{CP}^{r_j},\quad
X_i=S^{2n}\times Y_i,\quad
E_i=\mathbf1^n\oplus\bigoplus_{j<i}L_{j+1}^{\oplus r_j},
\quad A_i=\Gamma(\operatorname{End}E_i).
\tag{12}
\]
Then \(\operatorname{rank}E_i=r_i\) and \(\dim X_i=2r_i\).
Let \(\pi_i:X_{i+1}\to X_i\) be coordinate projection. Choose
\(x_i\in X_i\) whose projections have dense tails in every earlier
base: project a countable dense sequence in the infinite product,
listing each point infinitely often. Identify \(E_i(x_i)\) with
\(\mathbb C^{r_i}\), and use the decomposition
\[
E_{i+1}=\pi_i^*E_i\oplus(E_i(x_i)\otimes L_{i+1})
\]
to define the unital injective maps
\[
\varphi_i(a)=\pi_i^*a\oplus(a(x_i)\otimes1_{L_{i+1}}).
\tag{13}
\]
The coordinate summand proves injectivity. Put
\(A^{(n)}=\varinjlim(A_i,\varphi_i)\).

For completeness, the structural arguments are independent of the
initial rank. Any nonzero positive section at stage \(k\) is nonzero
on an open subset of \(X_k\). A later \(x_i\) projects into that
subset; the next point-evaluation block is then nonzero at every
fiber. In a homogeneous endomorphism section algebra, a section
nonzero at every fiber is full. Thus every nonzero stage-positive
element is full at some later stage.

If \(J\) is a nonzero ideal of the limit, choose \(b\in J_+\) of
norm one and a positive stage approximation \(a\) with
\(\|a-b\|<1/8\). The nonzero element \((a-1/4)_+\) belongs to
\(J\), as seen in the quotient by \(J\). Its later fullness puts
the unit in \(J\). Hence the limit is simple.

It is separable, unital, nuclear, AH, and infinite-dimensional by
the building blocks and injectivity. Every \(X_i\) has only even
cells, so \(K^1(X_i)=0\). Morita equivalence for \(E_i\) and
K-theory continuity give \(K_1(A^{(n)})=0\).

Each stage has a nonempty compact tracial state space. A finite set
of trace-compatibility conditions is satisfied by restricting a
trace from its latest stage. Compactness therefore gives a compatible
family and a trace on the limit. Simplicity makes this trace faithful;
its matrix amplifications are faithful, proving stable finiteness.
Surjectivity of the trace restriction maps is not used.

Let \(v_n\) be the image of \(u_n\in A_0=M_n(C(S^{2n}))\).
At every stage its image is homotopic to
\(u_n\oplus1_{H_i}\), where \(H_i=E_i-\mathbf1^n\): under (13),
the new evaluation matrix contracts in the ordinary connected group
\(U(r_i)\), even after tensoring its path with \(L_{i+1}\).
Taking powers of this homotopy and applying (11) shows that the
image of \(v_n^k\) is non-null at every stage if \(n!\nmid k\).

A null-homotopy in a unital injective limit is detected at a finite
stage. Indeed, partition the path so adjacent unitaries are within
\(1/4\), approximate its finitely many vertices within \(1/100\)
in one common stage, keeping the endpoints exact, and take polar
unitaries there. They are within \(2/100\) of the original vertices.
Successive polar unitaries are at distance less than two and hence
can be joined inside that stage using the principal logarithm.
Concatenation gives the claimed finite-stage path.

Consequently \(v_n^k\notin U_0(A^{(n)})\) whenever \(n!\nmid k\).
The contraction of \(u_n^{n!}\) passes to the limit, as does the
one-stabilization contraction. This proves (1).

Finally, for any \(d\ge2\), choose \(n\) with \(d\mid n!\).
The unitary \(v_n^{n!/d}\) has component order exactly \(d\),
since \(n!\mid k(n!/d)\) holds exactly when \(d\mid k\).
This proves the stated corollary. \(\square\)

## Sources and scope

- Bott, *The stable homotopy of the classical groups*, Annals of
  Mathematics 70 (1959), especially p. 315, gives the unstable
  group in (10). [Original paper](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/bott4.pdf).
- Püttmann and Rigas, *Presentations of the first homotopy groups of
  the unitary groups*, Commentarii Mathematici Helvetici 78 (2003),
  §3, identifies the characteristic clutching generator and describes
  its factorial-power contraction. [Publisher's paper](https://ems.press/content/serial-article-files/42980?nt=1).
- Hatcher, *Vector Bundles and K-Theory*, §1.2, §2.3,
  Proposition 3.13 and Proposition 4.3, supplies clutching,
  projective-space K-theory, the Euler/top-Chern identity, and the
  integral sphere Chern-character normalization.
  [Author's text](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf).
- Schochet, *Topological methods for C*-algebras II*, Pacific Journal
  of Mathematics 98 (1982), pp. 443–444, supplies the torsion-free
  Künneth theorem. [Publisher's paper](https://msp.org/pjm/1982/98-2/pjm-v98-n2-p15-s.pdf).

No claim is made that one fixed algebra contains cyclic subgroups
of every finite order. The proof above only identifies a subgroup;
the subsequent [exact group calculation](stw59-exact-factorial-component-groups-2026-09-05.md)
proves that the entire group for this same family is \(\mathbb Z/n!\).
The construction has dimension-to-rank ratio two at
every stage and uses line-twisted endomorphism bundles. It does not
assert purity or membership in the untwisted diagonal AH class.
