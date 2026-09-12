# Every finite abelian group as the entire unitary component group of a simple AH algebra

Date: 5 September 2026. Complete argument, independently internally reviewed.
The [separate review](stw59-finite-abelian-independent-review-2026-09-05.md)
checked the gauge sequence, independent global Euler coordinates,
bundle gluing, generator transport, and the entire simple-limit group.
No unresolved gap was found; no external or formal verification is claimed.
This strengthens the LIX construction; it is not a second named-problem
solution or a claim of external verification.

## 1. The theorem

**Theorem.** For every finite abelian group \(G\), there is a separable,
simple, unital, nuclear, stably finite, infinite-dimensional AH algebra
\(A_G\) such that
\[
K_1(A_G)=0,\qquad U(A_G)/U_0(A_G)\cong G.
\tag{1.1}
\]
For nonzero \(G\), the construction gives explicit commuting unitaries
representing cyclic generators. Each generator becomes null-homotopic
after its first matrix stabilization.

The trivial group is realized by an infinite-dimensional UHF algebra:
finite matrix stages have connected unitary groups and zero \(K_1\),
and polar approximation and finite-stage path detection pass these
properties to the limit. Its remaining structural properties follow
from the usual unital full-matrix inductive system.

Write a nonzero finite abelian group as
\[
G=\bigoplus_{\alpha=1}^s\mathbb Z/d_\alpha,
\qquad d_\alpha\ge2.
\]
The construction below puts these cyclic factors into different arms
of one connected base. A global Euler-image calculation checks that
gluing the arms adds neither generators nor relations.

## 2. The gauge calculation for a finite CW base

We use the dimension-dependent gauge calculation in
[the exact factorial proof](stw59-exact-factorial-component-groups-2026-09-05.md),
Sections 2–4. Its obstruction-theoretic part applies to any connected
finite CW complex \(X\) of dimension \(2r\) with \(K^1(X)=0\),
and any complex rank-\(r\) vector bundle \(E\).

For \(F=E\oplus\mathbf1\), evaluation at the last unit section gives
the locally trivial principal bundle
\[
\mathcal G(E)\longrightarrow\mathcal G(F)
\longrightarrow\mathcal S(F).
\]
The sphere fiber is \(S^{2r+1}\). Its orientation local system is
trivial because the bundle is complex. Relative obstruction theory gives
\[
\pi_0\mathcal S(F)=0,
\qquad \pi_1\mathcal S(F)=H^{2r}(X;\mathbb Z).
\]
One more trivial-line addition has a 2-connected section space. The
complement-and-rotation argument in the cited proof consequently gives
\[
\pi_0\mathcal G(F)=K^1(X)=0,
\qquad \pi_1\mathcal G(F)=K^0(X).
\]
Thus
\[
\pi_0\mathcal G(E)
\cong H^{2r}(X;\mathbb Z)/\operatorname{im}\Lambda_E.
\tag{2.1}
\]
This is a group quotient: the boundary of the principal-bundle sequence
multiplies endpoint components when loops are concatenated, with at
most the opposite convention. Its source is abelian and the boundary
is onto, so that convention does not affect (2.1).

The map \(\Lambda_E\) is the integral relative Euler class of a section
loop. Clutching a loop of gauge transformations gives a bundle over
\(S^2\times X\); the coefficient of the \(S^2\) generator in its top
Chern class is \(\Lambda_E\). In rational cohomology its formula is
\[
\Lambda_E(\beta)=
\sum_{j=0}^r(-1)^{r-j}(r-j)!\,
c_j(E)\operatorname{ch}_{r-j}(\beta).
\tag{2.2}
\]
The class on the left is integral and natural under restriction. In
the spaces below, top cohomology is free abelian and restriction to
the closed manifold arms identifies it with \(\mathbb Z^s\), so the
integral class is determined by its armwise Chern-number evaluations.
No global fundamental class for the joined base is assumed.

## 3. A common rank and a connected joined base

Choose \(R=\max_\alpha d_\alpha\) and put
\(e_\alpha=R-d_\alpha\). Define
\[
M_\alpha=S^2\times\mathbb{CP}^{d_\alpha-1}
                    \times\mathbb{CP}^{e_\alpha},
\qquad
E_\alpha=\mathbf1^{d_\alpha}
                  \oplus L_\alpha^{\oplus e_\alpha}.
\tag{3.1}
\]
When \(e_\alpha=0\), the last factor is a point and the last bundle
summand is absent. Each arm has real dimension \(2R\), and its bundle
has rank \(R\). All cells are even-dimensional.

Choose a basepoint \(x_\alpha\) on the zero-cell of each arm, and set
\[
X_0=\bigvee_{\alpha=1}^s M_\alpha.
\]
Fix unitary identifications of the fibers \(E_\alpha(x_\alpha)\)
with \(\mathbb C^R\), identifying the first two trivial coordinates
in each arm. The bundles glue to a rank-\(R\) vector bundle \(E_0\)
on \(X_0\). This gluing is locally trivial at the wedge point: use
trivializing neighborhoods in the finitely many arms and identify
their common fibers by the chosen matrices. Moreover \(E_0\) has a
global trivial rank-two summand.

For an arbitrary product
\[
Y=\prod_{j=1}^\ell\mathbb{CP}^{a_j},\qquad
m=\sum_j a_j,\qquad H=\bigoplus_j L_j^{\oplus a_j},
\]
including the empty product, put
\[
X=X_0\times Y,
\qquad E=\operatorname{pr}_{X_0}^*E_0\oplus H,
\qquad r=R+m.
\tag{3.2}
\]
The arm inclusions \(M_\alpha\times Y\subset X\) induce an isomorphism
\[
H^{2r}(X;\mathbb Z)
\xrightarrow{\ \cong\ }
\bigoplus_\alpha H^{2r}(M_\alpha\times Y;\mathbb Z)
\cong\mathbb Z^s.
\tag{3.3}
\]
Indeed, all cellular groups are free and concentrated in even
degrees. Top cohomology of the wedge is the direct sum of the arm
top cohomologies; in the product only the top degree of both factors
can contribute to degree \(2R+2m\). Also \(K^1(X)=0\), by induction
over the even cells and the cellular K-theory exact sequence.

## 4. The exact Euler image has independent coordinates

On arm \(\alpha\), the pair \((X,E)\) restricts to
\[
S^2\times\mathbb{CP}^{d_\alpha-1}
       \times\mathbb{CP}^{e_\alpha}\times Y,
\qquad
\mathbf1^{d_\alpha}\oplus L_\alpha^{\oplus e_\alpha}\oplus H.
\]
This is exactly the finite-stage pair in
[the arbitrary-cyclic proof](stw59-exact-arbitrary-cyclic-component-groups-2026-09-05.md),
Section 3. Its Euler map has image \(d_\alpha\mathbb Z\). For
clarity, its coefficients have the form
\[
\frac{(d_\alpha+k)!}{(d_\alpha-1)!\prod b_j!}
=d_\alpha\binom{d_\alpha+k}{d_\alpha,b_1,\ldots,b_t},
\qquad \sum b_j=k.
\]
They are integral multiples of \(d_\alpha\). The Bott class of
the \(S^2\) factor times the distinguished tautological line on
\(\mathbb{CP}^{d_\alpha-1}\) attains \(\pm d_\alpha\), because
the remaining bundle has top Chern number \(\pm1\).

Naturality of (2.2) therefore gives
\[
\operatorname{im}\Lambda_E
\subseteq\bigoplus_\alpha d_\alpha\mathbb Z.
\tag{4.1}
\]
The reverse inclusion requires a global class with only one nonzero
Euler coordinate; separate armwise computations alone would not prove it.

Let \(\beta_\alpha\in\widetilde K^0(M_\alpha)\) be the product
of the \(S^2\) Bott class and that distinguished tautological line,
pulled back over \(\mathbb{CP}^{e_\alpha}\). It has virtual rank zero.
Collapse all other arms of \(X_0\) to its wedge point and pull back
\(\beta_\alpha\), then pull it back to \(X_0\times Y\). Denote the
result by \(\widehat\beta_\alpha\). On arm \(\alpha\) it is precisely
the attaining class above, and on every other arm it is zero: pullback
to a point of a rank-zero virtual class is zero. Consequently
\[
\Lambda_E(\widehat\beta_\alpha)
=(0,\ldots,0,\pm d_\alpha,0,\ldots,0).
\tag{4.2}
\]
Each class in (4.2) comes from an actual gauge loop at rank \(r+1\),
by the stable-range identification preceding (2.1). Equations
(4.1)–(4.2) prove
\[
\operatorname{im}\Lambda_E
=\bigoplus_\alpha d_\alpha\mathbb Z,
\qquad
\pi_0\mathcal G(E)\cong\bigoplus_\alpha\mathbb Z/d_\alpha.
\tag{4.3}
\]
This calculation excludes hidden relations coming from the common
intersection \(\{*\}\times Y\) of the arms.

## 5. Adding a tautological block preserves every component coordinate

Let \((X,E)\) be as in (3.2), of dimension \(2r\) and rank \(r\).
Put
\[
X'=X\times\mathbb{CP}^r,
\qquad E'=\operatorname{pr}_X^*E\oplus J,
\qquad J=L^{\oplus r}.
\]
Extension by the identity, \(g\mapsto\operatorname{pr}_X^*g\oplus1_J\),
gives a map of gauge/section fibrations. On section loops its map is
\(s\mapsto(s,0)\). On each manifold arm this multiplies the relative
Euler integer by
\(\langle c_r(J),[\mathbb{CP}^r]\rangle=\pm1\).

Here is the local-zero normalization. Extend a section loop over
\(D^2\) times its arm, with transverse isolated zeros in the interior,
and pair the extension \(S\) with \(\chi\sigma\), where \(\sigma\)
is a transverse section of \(J\) and \(\chi\) vanishes near the disk
boundary and is positive at every zero of \(S\). The zeros of
\((S,\chi\sigma)\) are the product zeros and their signs multiply.
This is the relative Euler number of the new section loop.

Naturality and the isomorphism (3.3) determine the global map: it is
coordinatewise multiplication by \(\pm1\), with no mixing of arms.
It therefore induces an isomorphism on the quotient (4.3).
The same argument works when a rank-\(e\) block \(L^{\oplus e}\)
over \(\mathbb{CP}^e\) is added, for any \(e\ge1\); rank and half
dimension both increase by \(e\), and its top Chern number is still
\(\pm1\). The case \(e=0\) is the identity map.

## 6. Explicit generators

On \(S^2\times\mathbb{CP}^{d_\alpha-1}\), take the unitary
\(u_{d_\alpha}\) pulled back along the degree-one collapse to
\(S^{2d_\alpha}\), as in the arbitrary-cyclic proof, Section 4.
It is based at the identity and represents the cyclic generator.
Extend it by the identity on \(L_\alpha^{\oplus e_\alpha}\)
over the remaining factor of \(M_\alpha\). Section 5 shows that
it still generates that arm's component group.

Define \(v_\alpha\in\mathcal G(E_0)\) by this unitary on arm
\(\alpha\) and the identity on all other arms. These definitions
agree at the wedge point. They commute pointwise, since distinct
ones can differ from the identity only on distinct arms.
The restriction map on component groups is the isomorphism (4.3),
so their classes are the prescribed cyclic generators.

The characteristic unitary \(u_{d_\alpha}\oplus1\) has a based
null-homotopy in \(U(d_\alpha+1)\). Use one global trivial line
from a second copy of \(E_0\), leave the unused directions fixed,
and use that homotopy on arm \(\alpha\). It is the identity at
the wedge point throughout, so it glues to the constant homotopy
on the other arms. This contracts
\(\operatorname{diag}(v_\alpha,1)\) in \(U(M_2(\Gamma(\operatorname{End}E_0)))\).

## 7. The simple AH limit

Set \(r_i=R2^i\) and
\[
X_i=X_0\times\prod_{j<i}\mathbb{CP}^{r_j},
\quad E_i=\operatorname{pr}_{X_0}^*E_0
                \oplus\bigoplus_{j<i}L_{j+1}^{\oplus r_j},
\quad B_i=\Gamma(X_i,\operatorname{End}E_i).
\]
Then \(\dim X_i=2r_i\) and \(\operatorname{rank}E_i=r_i\).
Choose evaluation points \(x_i\in X_i\) with dense projected tails
in every earlier base. One explicit choice lists each member of
a countable dense set of \(X_0\times\prod_{j\ge0}\mathbb{CP}^{r_j}\)
infinitely often and projects its \(i\)-th term to \(X_i\).

After identifying \(E_i(x_i)\) with \(\mathbb C^{r_i}\), define
\[
\varphi_i(a)=\pi_i^*a\oplus
                  \bigl(a(x_i)\otimes1_{L_{i+1}}\bigr).
\tag{7.1}
\]
These are unital injective homomorphisms, and
\(A_G=\varinjlim(B_i,\varphi_i)\). For each fixed unitary \(g\),
the matrix \(g(x_i)\) contracts to one inside \(U(r_i)\).
Tensor that path with \(L_{i+1}\); thus the induced component map
of (7.1) is the identity-extension map from Section 5. It is an
isomorphism of the entire finite group \(G\) at every stage.

For completeness, simplicity follows directly from the dense tails.
A nonzero positive stage section is nonzero on an open set. A later
evaluation point projects into that set, and its next evaluation
block is nonzero at every fiber, hence full in that homogeneous
stage. If a nonzero limit ideal contains a positive norm-one element,
approximate it within \(1/8\) by a positive stage element \(a\).
The nonzero cutdown \((a-1/4)_+\) lies in the ideal, as seen in
the quotient, and later fullness puts the unit in that ideal.

The blocks are separable nuclear homogeneous algebras, so the limit
is separable, unital, nuclear, and AH. Increasing matrix ranks in
injectively included blocks make it infinite-dimensional. Even-cell
K-theory, Morita equivalence, and continuity give \(K_1(A_G)=0\).
The nonempty compact stage trace spaces have a compatible family:
each finite set of compatibility conditions is met by a trace at
its latest stage followed by backward restriction. Compactness gives
a limit trace; simplicity makes it faithful. Its matrix amplifications
are faithful, so the algebra is stably finite.

Finally, the component group of the unital injective limit is the
direct limit of the stage component groups. Every limit unitary is
approximated within \(1/100\) by a stage element, whose polar unitary
is within \(2/100\) of it; distance below two gives a homotopy.
If a stage unitary contracts in the limit, partition its path into
steps smaller than \(1/4\), approximate the finitely many vertices
within \(1/100\) in a common later stage with endpoints exact, and
take polar unitaries. Their adjacent distances are below
\(1/4+4/100<2\), so principal logarithms give a null-homotopy in
that stage. These arguments prove both surjectivity and injectivity.
Therefore
\[
U(A_G)/U_0(A_G)
\cong\varinjlim(G,\text{isomorphisms})\cong G.
\]
The initial commuting generators retain their prescribed classes,
and their first matrix stabilizations retain their contractions.
This proves the theorem.

## References and scope

- [Exact factorial gauge calculation](stw59-exact-factorial-component-groups-2026-09-05.md),
  Sections 2–4: local principal-bundle charts, finite-rank stable
  gauge identification, and integral Euler normalization.
- [Exact arbitrary cyclic construction](stw59-exact-arbitrary-cyclic-component-groups-2026-09-05.md):
  the cyclic arm calculation and its explicit characteristic unitary.
- A. Hatcher, *Vector Bundles and K-Theory*, §2.2 and §3.3, for
  the cellular K-theory exact sequence and relative section obstruction
  theory; [author's text](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf).

The new point is the equal-dimension joined base together with the
independent global attaining classes (4.2). The construction realizes
finite abelian groups; no assertion about nonabelian component groups
or a new named-problem solution is made.
