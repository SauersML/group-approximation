# Exact unitary component groups for the factorial twisted AH family

Date: 2026-09-05. **Complete proof; internal mathematical review completed.**
This strengthens the previously proved factorial-order subgroup to the
entire unitary component group. No external verification is claimed.

The root reviewer checked the principal-bundle construction, the
section-space obstruction dimensions, the stable complement rotation,
the integral Euler normalization, the exact image n! Z, and both
directions of component-group continuity at the limit. No unresolved
gap was found. This review is separate from structural graph checking.

## 1. The finite-stage theorem

Let \(n\ge2\), let \(d_1,\ldots,d_\ell\) be positive integers,
and allow the empty list. Put
\[
Y=\prod_{j=1}^{\ell}\mathbb{CP}^{d_j},\qquad
m=\sum_jd_j,\qquad
H=\bigoplus_{j=1}^{\ell}L_j^{\oplus d_j},
\]
where \(L_j\) is the tautological line from the indicated factor.
On
\[
X=S^{2n}\times Y
\]
let
\[
E=\mathbf1^n\oplus H,\qquad r=n+m.
\]
Thus \(\operatorname{rank}E=r\) and \(\dim_{\mathbb R}X=2r\).
Write
\[
\mathcal G(E)=U(\Gamma(X,\operatorname{End}E))
\]
for the group of unitary bundle automorphisms, with the uniform topology.

**Theorem 1.**
\[
\pi_0\mathcal G(E)\cong\mathbb Z/n!.
\tag{1.1}
\]
If \(u_n:S^{2n}\to U(n)\) is the generator fixed in the factorial
manuscript, then \(u_n\oplus1_H\) generates this group.

The existence of an element of order \(n!\) was proved in
[the factorial manuscript](stw59-factorial-torsion-simple-ah-manuscript-2026-09-05.md),
equation (11). The new assertion is that there are no other
components: the whole group is cyclic of that order.

The proof computes the exact sequence of the one-line
stabilization fibration, including the integral image of its
fundamental-group map.

## 2. The gauge-to-section fibration

Put \(F=E\oplus\mathbf1\), and let \(e\) be the constant unit
section of its last summand. Let \(\mathcal S(F)\) be the
space of unit sections of \(F\), again with the uniform topology.

**Lemma 2.** There is a locally trivial principal bundle
\[
\mathcal G(E)\longrightarrow\mathcal G(F)
\xrightarrow{\ \epsilon\ }\mathcal S(F),
\qquad \epsilon(g)=ge.
\tag{2.1}
\]
Furthermore,
\[
\pi_0\mathcal S(F)=0,\qquad
\pi_1(\mathcal S(F),e)\cong H^{2r}(X;\mathbb Z)\cong\mathbb Z.
\tag{2.2}
\]

**Proof.** The unit-sphere bundle of \(F\) has fiber
\(S^{2r+1}\). Its structure group is unitary, so its action
on the top homotopy group of that sphere preserves orientation.
Because \(\dim X=2r\), obstruction theory shows that all its
unit sections are homotopic: extending a section homotopy over
\(X\times[0,1]\) encounters no obstruction in this dimension.

We explain the local lifting rather than assume a fibration
property for section spaces. If unit sections \(s,t\) are
uniformly sufficiently close, write \(P=ss^*\) and \(Q=tt^*\).
The bundle endomorphism
\[
T=QP+(1-Q)(1-P)
\]
is invertible when \(\|P-Q\|<1\), since
\[
T^*T=1-(P-Q)^2.
\]
Its polar unitary \(h\) sends the line of \(s\) onto the line
of \(t\). There is a continuous scalar unitary \(c(x)\) with
\(h(x)s(x)=t(x)c(x)\). Multiplying \(h\) on the left by
\[
t c^{-1}t^*+(1-Q)
\]
gives a bundle unitary \(k(t,s)\) carrying \(s\) to \(t\).
It depends continuously on the close pair and equals the
identity when \(t=s\).

This gives local lifts of \(\epsilon\). Every section belongs
to its image: lift a homotopy from \(e\) to that section through
finitely many such neighborhoods, using compactness of the
path parameter. The stabilizer of \(e\) is exactly
\(\mathcal G(E)\). The local lifts give the principal-bundle
charts for (2.1), and in particular the homotopy lifting
property needed for its exact sequence.

A based loop of sections is a unit section on
\([0,1]\times X\) equal to \(e\) on its two boundary slices.
Since the sphere fiber is \(2r\)-connected and the parameter
space has dimension \(2r+1\), its sole difference obstruction
is
\[
H^{2r+1}([0,1]\times X,\{0,1\}\times X;\mathbb Z)
\cong H^{2r}(X;\mathbb Z).
\]
There are no higher obstructions in this dimension. Loop
concatenation adds the obstruction. The last group is
\(\mathbb Z\), with orientation generator, proving (2.2).
The elementary relative obstruction theory used here is
described in [Hatcher, §3.3]. \(\square\)

It follows that the relevant exact sequence is
\[
\pi_1\mathcal G(F)\xrightarrow{\epsilon_*}\mathbb Z
\xrightarrow{\partial}\pi_0\mathcal G(E)
\longrightarrow\pi_0\mathcal G(F).
\tag{2.3}
\]

## 3. Stable gauge groups and the range needed here

**Lemma 3.** In the present dimensions,
\[
\pi_0\mathcal G(F)\cong K^1(X)=0,\qquad
\pi_1\mathcal G(F)\cong K^0(X).
\tag{3.1}
\]
Under the second isomorphism, a based loop \(g\) corresponds
to the \(K^0(X)\)-coefficient of its sphere-clutched bundle.

**Proof.** First consider stabilization by another trivial line:
\[
\mathcal G(F)\longrightarrow\mathcal G(F\oplus\mathbf1)
\longrightarrow\mathcal S(F\oplus\mathbf1).
\]
Its sphere fiber is \(S^{2r+3}\). Since \(\dim X=2r\),
the section space is \(2\)-connected. Indeed, for \(j=0,1,2\),
a based \(j\)-parameter family extends over a \((j+1)\)-disk:
the first possible obstruction has degree \(2r+4\), larger
than the dimension \(2r+j+1\) of the extension problem.
The same statement holds after every further trivial-line
addition. The homotopy exact sequences consequently show that
both \(\pi_0\) and \(\pi_1\) are unchanged by these additions.

Here is an explicit justification of the stable gauge-group
identification, including the fact that we are adding trivial
lines rather than copies of \(F\). Choose a complementary bundle
\(F'\) and a trivialization
\[
F\oplus F'\cong\mathbf1^N.
\]
Extending a unitary of \(F\oplus\mathbf1^k\) by \(1_{F'}\)
gives a unitary of the trivial bundle \(\mathbf1^{N+k}\).
Conversely, a unitary of \(\mathbf1^k\) can be extended by
\(1_F\) to an automorphism of \(F\oplus\mathbf1^k\).

On stable homotopy classes these constructions are inverse.
One composite is ordinary stabilization by \(\mathbf1^N\).
For the other, the resulting automorphism acts on the old
copy of \(F\), while an additional copy of \(F\) is fixed;
the pair \(F\oplus F'\) is a trivial stabilization. Exchanging
the two copies of \(F\) by the usual continuous two-by-two
rotation moves the automorphism to the original copy.
This rotation works also when that automorphism has
off-diagonal blocks involving the added trivial summands,
since it is conjugation by a continuous unitary on the
whole enlarged bundle. Thus the second composite is
homotopic to trivial-line stabilization as well.

Therefore
\[
\varinjlim_k\pi_j\mathcal G(F\oplus\mathbf1^k)
\cong\varinjlim_k\pi_j U(C(X,M_k)).
\]
This is a statement about stable homotopy classes represented
at finite ranks; no assumption about compact sets in an
unspecified direct-limit topology is being made. For \(j=0\)
the right side is \(K^1(X)\), and for \(j=1\) it is
\(K^0(X)\), by Bott periodicity and suspension. The
previous paragraph shows that \(\pi_0\) and \(\pi_1\) already
have these values at \(\mathcal G(F)\).

All cells of \(X\) are even-dimensional, so the cellular
\(K\)-theory exact sequence gives \(K^1(X)=0\).

For the final assertion, clutch the pullback of \(F\) over the
two disks of \(S^2\) by a based loop \(g\) of its automorphisms.
Stabilizing the bundle and the loop converts this to ordinary
matrix-unitary clutching. The standard suspension/Bott
description of \(\pi_1 U(C(X)\otimes\mathcal K)\) identifies
the reduced class of that clutched bundle with the external
product of the Bott class on \(S^2\) and an element of
\(K^0(X)\). The complement-and-rotation argument above
shows that the same identification applies before stabilization.
\(\square\)

In particular, (2.3) yields
\[
\pi_0\mathcal G(E)
\cong\mathbb Z/\operatorname{im}(\epsilon_*).
\tag{3.2}
\]
This is an isomorphism of groups. In the homotopy sequence
of the principal bundle, lifting concatenated loops multiplies
the endpoint components in the stabilizer, with at most the
opposite convention. Since the source group is \(\mathbb Z\),
the resulting quotient is cyclic in either convention.

## 4. The integral normalization of the map \(\epsilon_*\)

Let \(g:S^1\to\mathcal G(F)\) be based at the identity. Form a
rank-\((r+1)\) bundle \(W_g\) on \(S^2\times X\) by clutching
the two pullbacks of \(F\), with convention
\[
(\xi,z)_+\sim(g(z)^{-1}\xi,z)_-
\quad (z\in S^1).
\tag{4.1}
\]
A section equal to \(e\) on the minus disk therefore has
boundary value \(g(z)e\) on the plus disk.

The integer in \(\pi_1\mathcal S(F)\) of the loop \(g(z)e\)
is the relative Euler number of \(F\) over \(D^2\times X\)
with this boundary section. Its equality with the
obstruction normalization in Lemma 2 can be checked in
one top cell: on a trivial real bundle of rank \(2r+2\),
the boundary unit section of degree one has relative
Euler number one. The complex orientation makes the
coefficient system untwisted.

Extend the boundary section over the plus disk, allowing
zeros, and leave the section \(e\) nonvanishing on the
minus disk. Their glued section of \(W_g\) has the same
zero indices. Since the Euler class of a complex bundle
is its top Chern class, we obtain, with compatible choices
of orientation,
\[
\epsilon_*([g])
=
\left\langle c_{r+1}(W_g),[S^2\times X]\right\rangle.
\tag{4.2}
\]
Reversing the fixed clutching or orientation convention
changes the sign throughout, but not the image subgroup.
There is no factorial in this Euler normalization; the
factorial will arise from the Chern-character identity.

Let \(\ell\) be a line bundle on \(S^2\) with
\(z=c_1(\ell)\) an integral generator, and set
\(b=[\ell]-1\). Write
\[
\delta=[W_g]-[F].
\]
The split restriction sequence and the torsion-free
Künneth theorem give a unique \(\beta\in K^0(X)\) such that
\[
\delta=b\,\beta,\qquad
\operatorname{ch}(\delta)=z\,\operatorname{ch}(\beta).
\tag{4.3}
\]
All bundles pulled back to products are denoted by the
same symbols. The sign convention may replace \(\beta\)
by its negative. Lemma 3 says that every \(\beta\in K^0(X)\)
is realized by an actual loop \(g\) at rank \(r+1\).

Because \(z^2=0\), the Chern-character/Newton identity gives
\[
c_q(\delta)=(-1)^{q-1}(q-1)!\operatorname{ch}_q(\delta).
\tag{4.4}
\]
Indeed, use
\(\log c(\delta)=\sum_{q\ge1}(-1)^{q-1}(q-1)!
\operatorname{ch}_q(\delta)\); every product of terms
in the logarithm vanishes, so exponentiation introduces
no additional terms.

Since \(c(F)=c(E)=c(H)\), equations (4.2)–(4.4) show that,
up to the single fixed orientation sign,
\[
\epsilon_*(\beta)=
\left\langle
\sum_{j=0}^{m}
(-1)^{r-j}(r-j)!\,
c_j(H)\operatorname{ch}_{r-j}(\beta),
[X]\right\rangle.
\tag{4.5}
\]

## 5. Computing the image exactly

Choose a Bott generator
\[
\kappa\in\widetilde K^0(S^{2n})
\]
whose Chern character is an integral orientation generator
\(x\in H^{2n}(S^{2n};\mathbb Z)\).
This normalization, with coefficient one, is
[Hatcher, Proposition 4.3]. The top Chern class of the
Bott generator has the corresponding factorial; its
Chern character does not.

The projective-space \(K\)-ring and Künneth theorem give
\[
K^0(X)=K^0(Y)\oplus\kappa K^0(Y).
\tag{5.1}
\]
Only the second summand contributes to (4.5), since
every other factor in that formula is pulled back
from \(Y\). Write
\[
\beta=\beta_0+\kappa\beta_1.
\]
The group \(K^0(Y)\) is additively generated by line
monomials \(\prod_iL_i^{a_i}\). For one such monomial
\(\beta_1\),
\[
\operatorname{ch}(\kappa\beta_1)
=x\exp\Bigl(\sum_i a_i h_i\Bigr),
\qquad h_i=c_1(L_i).
\]
In the \(j\)-th summand of (4.5), put \(k=m-j\).
A coefficient before multiplication by the integral
class \(c_j(H)\) is
\[
\pm\frac{(n+k)!}{\prod_i b_i!}\prod_i a_i^{b_i},
\qquad \sum_i b_i=k.
\tag{5.2}
\]
Its factorial ratio is
\[
\frac{(n+k)!}{\prod_i b_i!}
=
n!\binom{n+k}{n,b_1,\ldots,b_\ell},
\tag{5.3}
\]
an integral multiple of \(n!\). Multiplication by
\(c_j(H)\) preserves integral divisibility. Integer
linear combinations of line monomials therefore give
\[
\operatorname{im}(\epsilon_*)\subset n!\mathbb Z.
\tag{5.4}
\]
The cohomology of \(S^2\times X\) is torsion-free,
so these coefficient computations prove integral
divisibility rather than only rational equality.

For the reverse inclusion take
\[
\beta=\kappa,\qquad \beta_1=1.
\]
The only nonzero summand in (4.5) is \(j=m\), giving
\[
\epsilon_*(\kappa)
=
(-1)^n n!\left\langle x\,c_m(H),[X]\right\rangle
=\pm n!.
\tag{5.5}
\]
Here
\[
c_m(H)=\prod_i h_i^{d_i},
\qquad
\left|\langle c_m(H),[Y]\rangle\right|=1.
\]
The realization assertion in Lemma 3 ensures that
(5.5) is the value of an actual loop of rank-\((r+1)\)
gauge transformations, not merely a virtual stable
class. Thus
\[
\operatorname{im}(\epsilon_*)=n!\mathbb Z.
\tag{5.6}
\]

Combining (3.2) and (5.6) proves (1.1).
The unitary \(u_n\oplus1_H\) has order exactly \(n!\)
by equation (11) of the factorial manuscript.
It therefore generates the cyclic group just computed.
This completes the proof of Theorem 1. \(\square\)

## 6. The entire component group of the simple limit

Retain the explicitly defined factorial family
\(A^{(n)}\) of the preceding manuscript:
\[
r_i=n2^i,\quad
X_i=S^{2n}\times\prod_{j<i}\mathbb{CP}^{r_j},\quad
E_i=\mathbf1^n\oplus\bigoplus_{j<i}L_{j+1}^{\oplus r_j},
\quad
A_i=\Gamma(\operatorname{End}E_i).
\]
Its unital injective maps are
\[
\varphi_i(a)=\pi_i^*a\oplus
\bigl(a(x_i)\otimes1_{L_{i+1}}\bigr),
\]
with dense-tail evaluation points, and
\(A^{(n)}=\varinjlim(A_i,\varphi_i)\).

**Corollary 4.** For the simple unital nuclear stably finite
AH algebra \(A^{(n)}\),
\[
K_1(A^{(n)})=0,\qquad
U(A^{(n)})/U_0(A^{(n)})\cong\mathbb Z/n!.
\tag{6.1}
\]
The class of the original witness \(v_n\) generates the
entire component group.

**Proof.** Theorem 1 applies at every stage and identifies
its group with \(\mathbb Z/n!\), generated by
\(u_n\oplus1_{H_i}\). Applying a connecting map to this
unitary gives its coordinate copy plus a constant
evaluation matrix tensored with the new line bundle.
That finite-dimensional matrix contracts to the
identity through unitary matrices. Tensoring the
path with the line bundle gives a homotopy to
\(u_n\oplus1_{H_{i+1}}\). Thus every connecting map
takes the chosen generator to the chosen generator,
and induces an isomorphism on the entire component
group.

The component group of a unital injective limit is
the direct limit of the component groups here.
Injectivity is the finite-stage null-homotopy
detection argument in the preceding manuscripts:
approximate a finite partition of a unitary path,
take polar unitaries in one common stage, and join
adjacent vertices by logarithms.

For completeness, surjectivity also holds. If \(a\)
is a unitary in the limit, choose a stage element
\(b\) with \(\|b-a\|<1/100\). Both \(b^*b\) and
\(bb^*\) are within \(2/100+1/10000<1\) of the
unit, so \(b\) is invertible in that stage.
Its polar unitary \(q\) satisfies
\(\|q-a\|<2/100<2\). The principal logarithm of
\(a^*q\) supplies a unitary path from \(a\) to \(q\)
in the limit. Every limit component is therefore
represented at a finite stage.

Consequently the component group is the constant
direct system \(\mathbb Z/n!\), proving (6.1).
The structural properties and \(K_1=0\) are those
already established for this same inductive system
in the factorial manuscript. \(\square\)

For \(n=2\), this computes the entire component group
of the original LIX counterexample as \(\mathbb Z/2\).
For larger \(n\), it computes the whole factorial
group, not only a subgroup or a lower bound on its size.
It does not assert realization of every finite group
as the entire component group.

## References and proof dependencies

1. [The factorial manuscript](stw59-factorial-torsion-simple-ah-manuscript-2026-09-05.md),
   equation (11) for the exact order of the chosen finite-stage
   generator, and Section 3 for the simple inductive system.
2. A. Hatcher, *Vector Bundles and K-Theory*, version 2.2,
   §1.2 for clutching, §2.3 for projective-space \(K\)-theory,
   §3.3 for relative obstruction theory, Proposition 3.13
   for Euler/top-Chern identification, and Proposition 4.3
   for the integral Bott Chern-character normalization.
   [Author's text](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf).
3. C. Schochet, *Topological methods for C*-algebras II:
   Geometric resolutions and the Künneth formula*,
   Pacific J. Math. 98 (1982), 443–458, Künneth Theorem,
   used in the torsion-free finite-CW case.
   [Publisher's paper](https://msp.org/pjm/1982/98-2/pjm-v98-n2-p15-s.pdf).
4. R. Bott, *The stable homotopy of the classical groups*,
   Ann. of Math. 70 (1959), 313–337, for Bott periodicity
   and the unstable unitary calculation underlying the
   previously fixed generator.
   [Original paper](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/bott4.pdf).
