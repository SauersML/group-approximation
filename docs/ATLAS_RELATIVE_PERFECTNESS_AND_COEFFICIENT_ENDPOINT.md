# Relative perfectness and the finite-coefficient endpoint

Date: 2026-08-12

## 1. Outcome

The proposed pure group-theoretic globalization of the rank-three boundary
relations is impossible for the genuine binary Leavitt atlas.  There are two
exact branches of the same boundary relations:

* the classical branch, in which the two copies of
  \(H\cong GL_3(2)\) are amalgamated; and
* the genuine Leavitt branch, in which those copies are not identified.

Moreover, the natural amalgamation kernel is relatively perfect.  Therefore
the boundary group cannot be a nontrivial central extension of the amalgam:
if its kernel over the amalgam were central, that kernel would be trivial.

Consequently, neither Bass--Serre stability nor classification of arbitrary
exact finite-tracial representations can prove the desired alignment.  Any
successful theorem must use approximation by finite matrices, equivalently a
Connes-embeddability hypothesis.

The sharp surviving target is a finite-coefficient extraction theorem.  It
would turn a sufficiently accurate two-chart matrix microstate into an
approximate binary Leavitt family inside the finite multiplicity algebra.  A
one-line normalized-trace obstruction would then give a dimension-independent
gap and prove that the atlas group is nonhyperlinear.

## 2. The amalgamation kernel is relatively perfect

Let

\[
 P=A_{8,1}*A_{8,2},
 \qquad
 A=A_8*_H A_8,
 \qquad
 K=\ker(P\twoheadrightarrow A),
 \tag{RPC1}
\]

where the second copy has first been put in the fixed classical alignment.
Both \(A_8\) and \(H\cong PSL_2(7)\) are perfect.  The Mayer--Vietoris
sequence for the amalgam contains

\[
 H_2(H;\mathbf Z)
 \longrightarrow H_2(A_8;\mathbf Z)\oplus H_2(A_8;\mathbf Z)
 \longrightarrow H_2(A;\mathbf Z)
 \longrightarrow H_1(H;\mathbf Z)=0.
 \tag{RPC2}
\]

Hence the middle map onto \(H_2(A;\mathbf Z)\) is surjective.  On the other
hand,

\[
 H_2(P;\mathbf Z)
 \cong H_2(A_8;\mathbf Z)\oplus H_2(A_8;\mathbf Z),
 \tag{RPC3}
\]

and the map induced by \(P\twoheadrightarrow A\) is the map in `(RPC2)`.
Thus

\[
 H_2(P;\mathbf Z)\twoheadrightarrow H_2(A;\mathbf Z).
 \tag{RPC4}
\]

The five-term exact sequence of

\[
 1\longrightarrow K\longrightarrow P\longrightarrow A\longrightarrow1
\]

now gives

\[
 H_2(P;\mathbf Z)\longrightarrow H_2(A;\mathbf Z)
 \longrightarrow K/[P,K]
 \longrightarrow H_1(P;\mathbf Z)=0.
 \tag{RPC5}
\]

Surjectivity in `(RPC4)` implies

\[
 \boxed{K=[P,K].}
 \tag{RPC6}
\]

This calculation uses no atlas enumeration.

## 3. A central kernel would have to vanish

Let \(B_\partial=P/N\) be the genuine boundary group, with \(N\) the normal
closure of the compressed centrality relators.  Every boundary collision word
vanishes in the classical amalgam, so there is a natural surjection

\[
 B_\partial\twoheadrightarrow A.
 \tag{RPC7}
\]

Equivalently, \(N\subseteq K\).  If the kernel \(K/N\) of `(RPC7)` were
central in \(P/N\), then

\[
 [P,K]\subseteq N.
 \tag{RPC8}
\]

By `(RPC6)`, this says \(K\subseteq N\).  Since \(N\subseteq K\), one gets
\(N=K\).  Therefore

\[
 \boxed{
   \ker(B_\partial\to A)\text{ central}
   \quad\Longrightarrow\quad
   B_\partial\cong A_8*_H A_8.
 }
 \tag{RPC9}
\]

In particular, there is no intermediate nontrivial finite-central case in
this natural presentation.  In fact the proof excludes a nontrivial central
kernel of any cardinality; finiteness is not used.

## 4. The genuine Leavitt branch disproves amalgamation

The binary Leavitt atlas group \(Q\) is a quotient of \(B_\partial\), since
the collision words are genuine atlas relations.  However, its aligned
copies of \(H\) are distinct.

Use the two leaf charts

\[
 D_1=(01,1,000,001),
 \qquad
 D_2=(00,1,010,011).
 \tag{RPC10}
\]

For the transvection \(x_{12}=I+E_{12}\in H\), chart one gives

\[
 x_{12}^{(1)}=1+(01)(1)^*.
 \tag{RPC11}
\]

The fixed alignment swaps the first and third coordinates, so the aligned
chart-two element is

\[
 x_{12}^{(2,\mathrm{aligned})}=1+(010)(1)^*.
 \tag{RPC12}
\]

These operators are distinct in the faithful standard path model.  On a
path with prefix \(1\), `(RPC11)` adds the path with prefix \(01\), whereas
`(RPC12)` adds the path with prefix \(010\).  Hence

\[
 x_{12}^{(2,\mathrm{aligned})}(x_{12}^{(1)})^{-1}\ne1
 \quad\text{in }Q.
 \tag{RPC13}
\]

Thus \(B_\partial\not\cong A\).  Combining this with `(RPC9)` proves

\[
 \boxed{ker(B_\partial\to A)\text{ is noncentral}.}
 \tag{RPC14}
\]

This is an explicit nonlinear branch, not a hypothetical remote component
suggested by numerical optimization.

## 5. Exact finite-tracial alignment is false

Apply the left regular representation of \(Q\) in its finite group von
Neumann algebra \(L(Q)\).  Each chart restriction has the regular character:

\[
 \tau(\lambda_Q(g))=
 \begin{cases}
 1,&g=1,\\
 0,&g\ne1.
 \end{cases}
 \tag{RPC15}
\]

All atlas and boundary relations hold exactly, while `(RPC13)` remains
nontrivial.  Therefore the implication

\[
 \text{exact finite-tracial boundary solution}
 \Longrightarrow H\text{-alignment}
 \tag{RPC16}
\]

is false.  Any valid replacement must distinguish Connes-embeddable finite
tracial algebras from arbitrary finite tracial algebras.

The correct matrix-specific form is:

\[
 \boxed{
 \begin{array}{c}
 \pi:P\to\prod_\omega M_{20160k_n}(\mathbf C),\\
 \pi|_{A_{8,i}}\text{ has the canonical regular chart trace},\\
 \text{and the selected atlas relations hold exactly}
 \end{array}
 \Longrightarrow
 \pi(H_1)=\pi(k_0H_2k_0^{-1}).
 }
 \tag{RPC17}
\]

For boundary relations alone, `(RPC17)` is already refuted by the finite
affine countermodel in `ATLAS_BOUNDARY_RANK_THREE_EXACT_AUDIT.md`.  A live
version must include a sufficient interior packet, plausibly beginning with
collision word 19243.

## 6. What the rank-167 calculation actually controls

For the fold \(H_1*H_2\twoheadrightarrow H\), its kernel \(F\) is a free
group of rank \(|H|-1=167\).  A free basis is

\[
 d_h=h_2h_1^{-1},
 \qquad h\in H\setminus\{1\}.
 \tag{RPC18}
\]

Conjugation by the first copy is explicit:

\[
 g d_h g^{-1}=d_g^{-1}d_{gh}.
 \tag{RPC19}
\]

Thus \(F_{\mathrm{ab}}\) is the augmentation module of \(H\).  The four
surviving boundary orbits found in the exact computation span all 167
augmentation directions, with rank increments

\[
 105, 50, 6, 6.
 \tag{RPC20}
\]

This explains the full tangent rigidity: every abelianized discrepancy is
killed.  It does not exclude a nonlinear branch living in a perfect quotient
of \(F\), and the Leavitt quotient exhibits precisely such global behavior.

## 7. The finite-coefficient extraction target

In a canonical finite matrix model, write

\[
 \mathbf C^{20160k}\cong\ell^2(A_8)\otimes\mathbf C^k,
 \qquad
 U=(U_{x,y})_{x,y\in A_8},
 \tag{RPC21}
\]

where \(U_{x,y}\in M_k(\mathbf C)\), and define

\[
 D(U)=C^*(U_{x,y}:x,y\in A_8)\subseteq M_k(\mathbf C).
 \tag{RPC22}
\]

The desired bridge is the following quantitative statement.

> **Finite-coefficient Leavitt extraction.**  There are a fixed finite atlas
> packet \(\mathcal R\), constants \(C,c>0\), and fixed bounded recipes in
> the block coefficients such that, whenever the normalized
> Hilbert--Schmidt atlas defect is \(\delta\), the recipes produce
> \(X_0,Y_0,X_1,Y_1\in D(U)\) satisfying
> \[
> \max\bigl\{
> \|X_0Y_0-I\|_{2,k},
> \|X_1Y_1-I\|_{2,k},
> \|Y_0X_0+Y_1X_1-I\|_{2,k}
> \bigr\}
> \le C\delta^c.
> \tag{RPC23}
> \]

The constants and recipes must be independent of \(k\).  Merely producing
elements in the ambient algebra, or proving an exact statement at bounded
\(k\), is insufficient.

The most structured candidate recipe is **root-character compression**.
Fourier-decompose the regular chart under carefully chosen finite elementary
abelian root subgroups.  Their character spaces have multiplicities
proportional to \(k\).  The Steinberg commutator web and the two prefix charts
should then define the four operators on one multiplicity space.  The burden
is to prove that these compressed operators are well defined and obey the
three relations in `(RPC23)` with a dimension-independent loss.

Equivalently, and more geometrically, seek projections \(e,e_0,e_1\) and
partial isometries \(v_0,v_1\) in one finite root-character multiplicity
corner such that

\[
 e_0e_1\approx0,
 \qquad e_0+e_1\approx e,
 \qquad v_i^*v_i\approx e,
 \qquad v_iv_i^*\approx e_i.
 \tag{RPC23a}
\]

The regular chart should force \(\operatorname{tr}(e)\) to be bounded below.
Cyclicity then makes `(RPC23a)` impossible in a finite coefficient algebra:
each equivalence gives \(\operatorname{tr}(e_i)\approx
\operatorname{tr}(e)\), whereas orthogonal additivity gives
\(\operatorname{tr}(e)\approx2\operatorname{tr}(e)\).  This is the
projection form of `(RPC24)` and is likely better adapted to finite-subgroup
Fourier compression.

One must not confuse the required orthogonality with its group-theoretic
shadow.  A Steinberg relation encoding a zero product, for example
\([x_{ij}(a),x_{jk}(b)]=1\) when \(ab=0\), gives commutation of the associated
unitaries.  It does **not** by itself imply that their negative spectral
projections are orthogonal.  The full cross-root packet must supply this
stronger identity; otherwise root-character extraction stalls at the same
additivity gap as direct coefficient extraction.

There is no conflict with the exact regular model in `L(Q)`.  After
restricting `lambda_Q` to a finite chart, the regular `A_8` representation
occurs with infinite multiplicity.  Its transition blocks therefore live
naturally in `B(ell^2)`, not in a finite coefficient algebra with a
normalized matrix trace.  The ambient algebra `L(Q)` is finite, but the
block-coefficient algebra need not inherit that finite trace.  This is the
precise finite-multiplicity distinction which `(RPC23)` must exploit.

Conversely, a recipe carried out entirely inside the ambient finite von
Neumann algebra by universal star-polynomial and tracial operations cannot
work: it would also apply to the exact model in `L(Q)`.  The extracted
operators must genuinely belong to the finite multiplicity algebra `D(U)`
or to a canonically traced finite root-character multiplicity corner.

Every finite matrix algebra has the elementary obstruction

\[
 \boxed{
 \max\bigl\{
 \|X_0Y_0-I\|_2,
 \|X_1Y_1-I\|_2,
 \|Y_0X_0+Y_1X_1-I\|_2
 \bigr\}\ge\frac13.
 }
 \tag{RPC24}
\]

Indeed, put \(e_i=X_iY_i-I\) for \(i=0,1\) and
\(e_2=Y_0X_0+Y_1X_1-I\).  Cyclicity of normalized trace gives

\[
 \operatorname{tr}(e_2)
 =1+\operatorname{tr}(e_0)+\operatorname{tr}(e_1).
 \tag{RPC25}
\]

Since \(|\operatorname{tr}(z)|\le\|z\|_2\), all three norms being strictly
less than \(1/3\) contradict `(RPC25)`.

Consequently `(RPC23)` would imply

\[
 \delta\ge (3C)^{-1/c}>0,
 \tag{RPC26}
\]

uniformly in \(k\).  This would rule out atlas microstates and prove that
\(Q\) is nonhyperlinear.

## 8. Exact burden and falsification gates

The phrase "extract the coefficients" is not yet a proof.  The following
are the minimum gates for `(RPC23)`.

1. **Explicit recipes.**  Express each \(X_i,Y_i\) as a fixed
   noncommutative polynomial, compression, or finite partial trace of block
   coefficients of \(U\).  The recipe cannot depend on \(k\).
2. **Uniform norm control.**  Bound every use of multiplication and
   compression in normalized Hilbert--Schmidt norm without a factor growing
   with \(k\).
3. **Additivity source.**  Identify exactly which group relations create the
   additive relation in `(RPC23)`.  Group microstates are multiplicative;
   additivity does not follow formally from approximate group relations.
4. **Interior necessity.**  The 234 boundary relations alone cannot suffice,
   because the affine finite countermodel satisfies them exactly.  Test the
   smallest boundary-plus-interior packet, starting with word 19243.
5. **Exact finite-model falsification.**  If a finite-dimensional exact
   regular-margin model of the selected packet exists, `(RPC23)` is false.
   Search for this before attempting a long quantitative proof.
6. **Ultraproduct closure.**  Verify that an \(o(1)\)-defect sequence turns
   the fixed recipes into exact Leavitt relations in the coefficient
   ultraproduct.  This is the cleanest logical formulation of the endpoint.

The highest-value next step is Gate 3: locate the finite atlas identities
whose block-matrix coefficients contain the two inverse relations and the
one additive Cuntz--Leavitt relation.  If no such identities survive taking
fixed coefficients or partial traces, the coefficient route should be
discarded rather than supported by further unrestricted optimization.

The simplest degree-one version of Gate 3 is already ruled out by the exact
radius-five scan.  After the fixed classical (H)-alignment, every collision
word has either zero or at least two transverse second-chart syllables; the
archived histogram has no entry at one.  Consequently the complete window
produces no relation of the form

\[
 W\lambda(a)=\lambda(b)W
 \tag{RPC26a}
\]

after merely commuting the (H)-syllables through (W).  This is recorded
by
`experiments/atlas_interior_single_bridge.py` and
`experiments/atlas-interior-single-bridge.json`, whose exact output has
`single_transverse_second_chart_equations=0`.  Thus the Hall or one-cut
support constraint must be extracted from genuinely quadratic-or-higher
block equations, or from a relation packet outside this collision tree; a
linear Hecke synchronization edge is not hidden in the current window.

There is a precise reason this extraction could distinguish the exact
Leavitt model from matrix microstates.  In the left regular representation of
\(Q\), decomposition over the finite chart gives an infinite coset
multiplicity space.  The transition coefficients naturally live in
\(B(\ell^2)\), a properly infinite algebra in which a binary Leavitt family
can exist.  In the canonical matrix model the corresponding multiplicity
space is \(\mathbf C^k\), and all extracted coefficients lie in the finite
algebra \(M_k(\mathbf C)\), where `(RPC24)` applies.  Thus finite
multiplicity, not ambient traciality, is the load-bearing hypothesis.

Conversely, an extraction carried out wholly inside the ambient finite von
Neumann algebra using universal star-polynomial operations cannot work: it
would also apply to the exact regular model in \(L(Q)\).  The construction
must retain the canonical finite multiplicity corner or coefficient trace.

## 9. The root-character pairing has infinite rank

There is an exact algebraic lemma which makes the root-character target
canonical.  Put \(R=L_{\mathbf F_2}(1,2)\), and let
\(\ell:R\to\mathbf F_2\) be an additive functional with \(\ell(1)=1\).
Define

\[
 b_\ell(a,b)=\ell(ab).
 \tag{RPC27}
\]

Then \(b_\ell\) has infinite rank.

Indeed, its left radical

\[
 \mathcal L_\ell=\{a\in R:\ell(ab)=0\text{ for every }b\in R\}
 \tag{RPC28}
\]

is a right ideal: if \(a\in\mathcal L_\ell\) and \(r,b\in R\), then
\(\ell((ar)b)=\ell(a(rb))=0\).  Moreover \(1\notin\mathcal L_\ell\), since
\(\ell(1)=1\).  If `(RPC27)` had finite rank, the nonzero quotient

\[
 V_\ell=R/\mathcal L_\ell
 \tag{RPC29}
\]

would be a finite-dimensional unital right \(R\)-module.  Right
multiplication by the Leavitt generators would then give endomorphisms of
\(V_\ell\) satisfying the binary Leavitt relations.  Taking ordinary
dimension, or matrix trace, gives \(\dim V_\ell=2\dim V_\ell\), a
contradiction.

Equivalently, for the additive character
\(\chi_\ell(r)=(-1)^{\ell(r)}\), the Heisenberg commutation pairing
\(\chi_\ell(ab)\) has infinite rank whenever \(\chi_\ell(1)=-1\).

This gives a precise reconstruction program.  In a canonical matrix
microstate, Fourier-decompose a central root subgroup and retain the
positive-trace sectors on which the constant root has character \(-1\).
The two adjacent root groups encode finite-dimensional truncations of
`(RPC27)`.  The desired stability theorem must show that sufficiently small
full-atlas defect makes the radical quotient of those truncations into an
approximate right \(R\)-module with positive normalized dimension.  The
right actions of \(s_i,t_i\) then supply `(RPC23)` or `(RPC23a)`.

There is a fixed finite Fourier corner in which to attempt this.  The scalar
root involutions

\[
 u=x_{12}(1),\qquad v=x_{23}(1),\qquad z=x_{13}(1)
 \tag{RPC30}
\]

generate the order-eight Heisenberg group, with \([u,v]=z\).  On the
\(z=-1\) spectral sector, its unique noncentral irreducible representation
gives a canonical factorization

\[
 e_-\mathcal H\cong\mathbf C^2\otimes\mathcal K,
 \tag{RPC31}
\]

where \(u,v\) act as Pauli matrices on \(\mathbf C^2\), and the coefficient
algebra acts on \(\mathcal K\).  In a canonical multiplicity-\(k\) atlas
model, \(\dim\mathcal K\) is a fixed multiple of \(k\).

Put \(p_i=s_it_i\), so \(p_0+p_1=1\), and consider
\(z_i=x_{13}(p_i)\).  The \(z_i\) commute with the group in `(RPC30)` and
therefore descend on `(RPC31)` to commuting coefficient involutions
\(\widehat z_i\).  Since \(z_0z_1=z\), on the \(z=-1\) sector one has

\[
 \widehat z_0\widehat z_1=-I.
 \tag{RPC32}
\]

Consequently the negative spectral projections of \(\widehat z_0\) and
\(\widehat z_1\) are complementary.  The required remaining identity is
that the compressor words associated with \(s_i,t_i\), after taking their
fixed Pauli blocks, give partial isometries from \(\mathcal K\) onto those
two complementary subspaces.  The sparse `rawInvolutionMatrix` already has
the relevant corner entries \(p_i,s_i,t_i\); hence this is a finite block
calculation rather than an unconstrained search over all \(20160^2\)
coefficients.

This last partial-isometry claim is not automatic from the group
commutators and has not been proved.  It is now the smallest concrete form
of the coefficient-extraction gate.

There is a useful exact calibration which prevents a tempting but false
shortcut at this point.  Let \(M\) be any finite tracial von Neumann algebra,
let \(z_0,z_1\in M\) be commuting self-adjoint involutions, and put

\[
 z=z_0z_1,\qquad e=P_-(z),\qquad e_i=P_-(z_i).
 \tag{RPC33}
\]

Assume that the two compression implementers conjugate \(z\) to \(z_i\).
Then

\[
 \tau(e_0)=\tau(e_1)=\tau(e)=:t.
 \tag{RPC34}
\]

Since the negative set of the product of two commuting signs is their
symmetric difference,

\[
 e=e_0(1-e_1)+(1-e_0)e_1.
 \tag{RPC35}
\]

Taking traces in `(RPC35)` gives the exact identity

\[
 \tau(e_0e_1)=\frac t2.
 \tag{RPC36}
\]

In the regular-character sector \(t=1/2\), all four joint sign projections

\[
 e_0e_1,\quad e_0(1-e_1),\quad (1-e_0)e_1,\quad
 (1-e_0)(1-e_1)
 \tag{RPC37}
\]

have trace \(1/4\).  Thus the two corner-root signs are exactly independent,
not orthogonal.  On the \(z=-1\) sector their negative projections are
complementary, but each occupies only one half of that sector.  The whole
compressor maps \(e\) onto \(e_i\); it does **not** map the Pauli multiplicity
space onto the half-sector \(ee_i\).

Consequently no trace contradiction follows from compression conjugacy and
`(RPC32)` alone.  A successful proof must identify a particular matrix
coefficient of the cross-chart implementer whose initial projection is the
Pauli multiplicity identity and whose final projection is the coefficient
projection cut out by \(ee_i\).  This is precisely the assertion which is
automatic for the sparse Leavitt matrix over an infinite coefficient space
and which still has to be derived from the finite atlas relations.

The lemma itself does not give the needed quantitative stability.  A matrix
sequence can realize larger and larger finite-rank pieces of an
infinite-rank pairing.  The missing estimate must prove a uniform boundary
cost for truncating the two self-similar copies; otherwise increasing
multiplicity can absorb the rank growth.

## 10. Status

Proved here:

* relative perfectness `(RPC6)`;
* collapse of the central-kernel alternative `(RPC9)`;
* the explicit nonamalgamated Leavitt branch `(RPC13)`--`(RPC14)`;
* failure of arbitrary exact finite-tracial alignment `(RPC16)`; and
* the matrix trace gap `(RPC24)`;
* infinite rank of every nontrivial root-character pairing `(RPC27)`.

Not proved:

* finite-coefficient extraction `(RPC23)`;
* CE rigidity `(RPC17)` for any sufficient full packet; or
* nonhyperlinearity of \(Q\).

## 11. A smaller finite-multiplicity target: triangular leakage

Full extraction `(RPC23)` is stronger than necessary.  The displayed comb
compressor is already one-sided triangular, and one-sided triangularity of a
unitary is impossible over a finite tracial multiplicity algebra unless all
off-diagonal blocks vanish.  The following quantitative form isolates the
finite-matrix invariant.

Let `(D,tau)` be a finite tracial von Neumann algebra and let

```text
e_1+...+e_m=1
```

be pairwise orthogonal projections.  Put `P_r=e_1+...+e_r`.  For every
unitary `W in M` one has

\[
 \|(1-P_r)WP_r\|_2^2=\|P_rW(1-P_r)\|_2^2.
 \tag{RPC38}
\]

Indeed, both sides equal

\[
 \tau(P_r)-\tau(P_rW^*P_rWP_r)
\]

after cyclically moving the factors on the second side.  Summing `(RPC38)`
over `r=1,...,m-1` gives

\[
 \sum_{i>j}(i-j)\|e_iWe_j\|_2^2
 =
 \sum_{i<j}(j-i)\|e_iWe_j\|_2^2.
 \tag{RPC39}
\]

Consequently

\[
 \boxed{
 \sum_{i<j}\|e_iWe_j\|_2^2
 \le (m-1)\sum_{i>j}\|e_iWe_j\|_2^2.}
 \tag{RPC40}
\]

In particular, an exactly upper-triangular unitary is block diagonal.  This
statement fails in the needed way on an infinite multiplicity space: a
proper isometry and coisometry can occupy the diagonal blocks of an upper
triangular unitary, and the projections in question have infinite ordinary
trace.  Thus `(RPC40)` distinguishes finite matrix microstates from the
exact Leavitt regular model without invoking an identity valid in every
finite ambient von Neumann algebra.

For the rank-four comb matrix

\[
 \begin{pmatrix}
 s_0&0&0&p_1\\
 0&s_0&0&p_1t_0\\
 0&0&s_0&p_1t_0^2\\
 0&0&0&t_0^3
 \end{pmatrix},
 \tag{RPC41}
\]

it is therefore enough to prove the following weaker replacement for
`(RPC23)`.

> **Finite flag-support extraction.**  From a canonical regular-margin atlas
> microstate of defect `delta`, construct a fixed four-step projection flag
> in a canonically traced finite multiplicity corner and a unitary `W` such
> that
> \[
>  \sum_{i>j}\|e_iWe_j\|_2^2\le C\delta^c,
>  \qquad
>  \sum_{i<j}\|e_iWe_j\|_2^2\ge c_0-C\delta^c
>  \tag{RPC42}
> \]
> for constants `C,c,c_0>0` independent of the multiplicity.

Equations `(RPC40)` and `(RPC42)` give an immediate positive defect floor.
Unlike `(RPC23)`, this target does not require identifying `s_i,t_i` as four
operators or reconstructing the additive Leavitt relation.  Unitarity itself
is the additivity source.  The only remaining work is support rigidity and a
positive-mass certificate for one upper block.

The natural support projections must be obtained from the finite scalar/root
subgroup by a fixed Fourier or parabolic compression.  Merely writing the
abstract ring matrix `(RPC41)` is not enough: a group microstate does not
come with the four module-coordinate projections.  The decisive finite test
is therefore whether the smallest boundary-plus-interior packet forces the
compressed image of the comb word to satisfy `(RPC42)`.  If it does, this
triangular-leakage argument proves nonhyperlinearity without the stronger
partial-isometry claim in `(RPC23a)`.

## 12. A sharper support-only obstruction: quantitative Hall deficiency

There is an even smaller success condition when the extracted block support
has a Hall deficit.  Let `(D,tau)` be a finite tracial von Neumann algebra,
let `W=(W_ij)` be a unitary in `M_m(D)`, and give `M_m(D)` its normalized
product trace.  For subsets `S,T subset {1,...,m}`, let `Q_S` be the diagonal
projection onto the source coordinates in `S` and `P_T` the diagonal
projection onto the target coordinates in `T`.  Then

\[
 \begin{aligned}
 \frac1m\sum_{j\in S}\sum_{i\notin T}\|W_{ij}\|_{2,D}^2
 &=\|(1-P_T)WQ_S\|_2^2\\
 &\ge \frac{(|S|-|T|)_+}{m}.
 \end{aligned}
 \tag{RPC43}
\]

Indeed,

\[
 \begin{aligned}
 \|(1-P_T)WQ_S\|_2^2
 &=\tau(Q_S)-\|P_TWQ_S\|_2^2\\
 &=\tau(Q_S)-\tau(P_TWQ_SW^*P_T)\\
 &\ge\tau(Q_S)-\tau(P_T),
 \end{aligned}
\]

because `0 <= P_TWQ_SW^*P_T <= P_T`.  This proves `(RPC43)`.  The same
argument works for arbitrary finite projection families, with
`(|S|-|T|)/m` replaced by `tau(Q_S)-tau(P_T)`.

Consequently, suppose a fixed Fourier compression of the atlas transition
unitary has an allowed-support graph `E` from source types to target types.
If some source set `S` has fewer allowed neighbours `N(S)` than its total
tracial weight, then

\[
 \sum_{j\in S}\sum_{i\notin N(S)}\|W_{ij}\|_{2,D}^2
\]

has a fixed positive lower bound.  Thus it is enough for a finite atlas
packet to force precisely those forbidden blocks to be `o(1)`.  No lower
bound on a selected upper block, no reconstruction of four Leavitt
operators, and no classification of the remaining blocks is needed.

This gives the sharpest immediate computational gate:

> **Finite Hall-support extraction.**  Fourier-decompose the fixed root
> Heisenberg/parabolic packet, compute the forced zero blocks of the two raw
> compressor intertwiners, and test the resulting finite weighted bipartite
> graph for a Hall-deficient source set.

There is a categorical restriction on this gate.  The projections in a
successful Hall graph cannot all be ambient spectral projections obtained by
universal star-polynomials in the group unitaries.  Otherwise the same exact
support inclusions would hold in the left regular representation inside the
finite tracial algebra `L(Q)`.  Applying `(RPC43)` there would already rule
out a Hall deficit.  Equivalently, if exact ambient relations give

\[
 WQ_SW^*\le P_{N(S)},
\]

then traciality itself gives

\[
 \tau(Q_S)=\tau(WQ_SW^*)\le\tau(P_{N(S)}).
 \tag{RPC43a}
\]

Thus the finite test must first disintegrate the canonical regular chart
`ell^2(A_8) tensor C^k` and take support in the finite coefficient or
multiplicity algebra.  That disintegration is not an intrinsic ambient
operation in `L(Q)`, whose corresponding multiplicity space is infinite.
Ambient subgroup Fourier projections may organize the calculation, but
they cannot themselves supply the deficient graph.

The visible support graph of the bare four-by-four comb matrix `(RPC41)` is
Hall-balanced: its diagonal already supplies a perfect matching.  Therefore
`(RPC43)` does not by itself prove anything from the printed triangular
matrix.  A successful deficit must occur only after the root-character or
Pauli compression which remembers the self-similar multiplicity types.
This is a useful falsification criterion: if every forced finite type graph
is Hall-balanced, support-only extraction is dead and one must return to the
stronger coefficient identities in `(RPC23)`.

## 13. One cut is enough

The four-step flag in `(RPC42)` is itself stronger than necessary.  For a
projection `P` and a unitary `W` in any finite tracial von Neumann algebra,
`(RPC38)` already says

\[
 \boxed{\|(1-P)WP\|_2=\|PW(1-P)\|_2.}
 \tag{RPC44}
\]

For the displayed comb matrix `(RPC41)`, take the algebraic coordinate cut

\[
 P=\operatorname{diag}(1,1,1,0).
 \tag{RPC45}
\]

Then the lower-left corner `(1-P)WP` is zero, whereas the upper-right corner
contains

\[
 p_1,\qquad p_1t_0,\qquad p_1t_0^2.
 \tag{RPC46}
\]

Consequently the minimal live extraction statement is now:

> **One-cut coefficient extraction.**  From a canonical regular-margin
> atlas microstate of defect `delta`, construct in a fixed matrix
> amplification of its finite multiplicity algebra a projection `P` and a
> unitary `W` such that
> \[
>  \|(1-P)WP\|_2^2\le C\delta^c,
>  \qquad
>  \|PW(1-P)\|_2^2\ge c_0-C\delta^c,
>  \tag{RPC47}
> \]
> for constants `C,c,c_0>0` independent of the multiplicity.

Equations `(RPC44)` and `(RPC47)` immediately give

\[
 c_0\le 2C\delta^c,
 \qquad
 \delta\ge(c_0/(2C))^{1/c}.
 \tag{RPC48}
\]

Thus neither all four Leavitt operators nor four Fourier sectors are needed.
One must extract only the rank-three-versus-one coordinate cut of the comb,
prove that its forbidden direction is small, and retain positive mass in one
allowed direction.  The natural candidate for the positive mass is the
`p_1` entry in `(RPC46)`; a root-character projection with its regular trace
bounded below would suffice.

The finite-multiplicity qualification is essential.  In the exact regular
representation of `Q`, the two chart restrictions again have regular finite
chart character, but the associated chart multiplicity space is infinite.
The coordinate cut `(RPC45)` then belongs to an amplification over
`B(ell^2)`, which has no normalized finite coefficient trace.  A recipe for
`P` made only from universal ambient von Neumann algebra operations would
also apply inside `L(Q)` and therefore cannot establish `(RPC47)`.  The
projection must be recovered in the canonical finite chart multiplicity
corner (or an equivalent finite root-character coefficient corner).

## 14. Root-tree covariance is Hall-balanced at every finite depth

The most obvious implementation of `(RPC43)` cannot work.  For a binary word
`alpha`, put

\[
 p_\alpha=s_\alpha t_\alpha,
 \qquad z_\alpha=x_{13}(p_\alpha).
 \tag{RPC49}
\]

At depth `r`, the projections `p_alpha`, `|alpha|=r`, are nonzero,
pairwise orthogonal, and sum to one.  Hence the root involutions `z_alpha`
generate an elementary abelian group

\[
 E_r\cong(C_2)^{2^r}.
 \tag{RPC50}
\]

Every nonempty product of the `z_alpha` is a nontrivial root element.  The
group trace restricted to `E_r` is therefore its regular character.  In a
putative hyperlinear atlas sequence, finite-group Hilbert--Schmidt
exactification makes the traces of the Fourier projections converge to the
regular values below.  Writing `n=2^r`, every character projection `e_chi`,
`chi in dual(E_r)`, has limiting normalized trace

\[
 \tau(e_\chi)=2^{-n}.
 \tag{RPC51}
\]

Let `C_i` be the compressor for the `i`th Leavitt branch.  Coefficient
compression gives

\[
 C_i z_\alpha C_i^*=z_{i\alpha}.
 \tag{RPC52}
\]

Consequently, if `f_psi` is a character projection for `E_(r+1)`, then

\[
 f_\psi C_i e_\chi=0
 \quad\text{unless}\quad
 \psi(i\alpha)=\chi(\alpha)
 \text{ for every }|\alpha|=r.
 \tag{RPC53}
\]

For each source character `chi`, the allowed targets are precisely its
`2^n` extensions obtained by freely choosing the signs on the other depth
`r+1` subtree.  Each target projection has trace `2^(-2n)`.  Therefore, for
every source set `S`, its allowed neighbourhood satisfies the exact weighted
identity

\[
 \tau\!\left(\sum_{\psi\in N(S)}f_\psi\right)
 =|S|2^n2^{-2n}
 =|S|2^{-n}
 =\tau\!\left(\sum_{\chi\in S}e_\chi\right).
 \tag{RPC54}
\]

Thus this finite type graph has no weighted Hall-deficient set at any depth.
The same calculation remains true on the negative source-root sector.  The
compressor sends
`z=product_(|alpha|=r) z_alpha` to the sign of the `i`th target subtree, not
to the product over both target subtrees.  Hence a negative source character
still has all `2^n` choices on the unused subtree, and `(RPC54)` remains
equal.  Conditioning the target on the global depth-`r+1` sign would discard
half those extensions, but no one-compressor covariance relation forces
that additional condition; treating it as automatic would be exactly the
false orthogonality shortcut ruled out by `(RPC33)`--`(RPC37)`.

This explains the independent-sign calibration `(RPC33)`--`(RPC37)` at all
levels.  Deeper central-root Fourier decomposition alone cannot prove
nonhyperlinearity.  A Hall deficit, if one exists, must use additional
support constraints from block coefficients of the raw second compressor and
noncentral adjacent roots, which couple the two freely extending subtrees
after canonical regular-chart disintegration.  Otherwise the live target
remains the positive-versus-forbidden one-cut estimate `(RPC47)`.

## 15. The gauge-fixing obstruction

There is a further qualification on every coefficient or support argument.
In the canonical criterion the second regular chart is

\[
 g\longmapsto U(\lambda(g)\otimes I_k)U^*.
 \tag{RPC55}
\]

The implementing unitary is not part of the represented group.  Replacing
it by

\[
 U C,\qquad C\in(\lambda(A_8)\otimes I_k)',
 \tag{RPC56}
\]

does not change a single chart matrix or relator value.  Thus the individual
blocks of `U` in the regular basis, their zero pattern, and the coefficient
algebra generated by a chosen collection of those blocks are not intrinsic
objects.  A relator packet cannot force a support statement about those
blocks until a gauge in `(RPC56)` has been selected.

This gives a sharp dichotomy for `(RPC47)`.

* If `P` and `W` are obtained by a gauge-invariant polynomial or von Neumann
  algebra operation on the two represented chart algebras, the same recipe
  applies to the exact nonaligned representation in `L(Q)`.  Since `L(Q)` is
  finite tracial, the leakage equality `(RPC44)` then rules out the desired
  asymmetry.
* If `P` and `W` use a chosen tensor identification
  `ell^2(A_8) tensor C^k`, the proof must show that some gauge `C` in
  `(RPC56)` can be chosen so that the one-cut inequalities hold.  This is a
  genuinely finite-dimensional matching or index theorem.  Merely expanding
  the printed Leavitt matrix in one preferred regular basis does not prove it.

The distinction also clarifies the exact Leavitt branch.  On `ell^2(Q)`, the
two restricted chart representations have infinite regular multiplicity, so
an intertwining unitary can be changed by an infinite commutant.  A
shift-type gauge can carry the missing index.  In a canonical matrix model
the corresponding multiplicity is finite, and the desired contradiction is
precisely that no finite gauge can carry the same index with vanishing
normalized boundary.

Therefore the smallest correct positive target is stronger than a raw block
audit and weaker than full coefficient-Leavitt extraction:

> **Finite gauge-index theorem.**  Every finite-multiplicity relative
> implementer satisfying the fixed atlas packet admits a commutant gauge for
> which one extracted cut has the asymmetric leakage `(RPC47)`, with constants
> independent of the multiplicity.

This is the load-bearing theorem behind the one-cut route.  A computation of
forced zeros in a single arbitrary gauge cannot substitute for it.

## 16. Two compressors do not create a Hall deficit by themselves

Using both binary branches appears at first to repair the balanced graph in
`(RPC54)`.  At depth `r`, take two copies of the source character set, one
for each compressor.  Their combined source weight is two, whereas the
depth-`r+1` target has weight one.  Thus the formal union of the two
covariance graphs has a `2:1` Hall surplus.

This is not yet an operator obstruction.  Equation `(RPC43)` applies to the
columns of one unitary or, more generally, to one contraction which is
isometric on the displayed source.  The two compressor group elements give
two separate unitaries.  Placing their columns side by side does not give an
isometry from two source copies: the missing condition is precisely that the
two columns have orthogonal ranges.

In exact coefficient notation that condition is the Leavitt relation.  If
`S_0,S_1` in a finite tracial algebra satisfied

\[
 S_i^*S_j=\delta_{ij}1,
 \tag{RPC57}
\]

then `S_0S_0^*` and `S_1S_1^*` would be orthogonal projections, while

\[
 \tau(S_0S_0^*)+\tau(S_1S_1^*)=2,
 \tag{RPC58}
\]

contradicting their sum being at most one.  The same argument has an
elementary quantitative version for approximately isometric, approximately
orthogonal columns.  But covariance of each compressor with the root tree
does not imply the cross term `S_0^*S_1` is small.

Therefore the two-branch refinement changes the smallest positive target,
but does not eliminate coefficient extraction:

> **Cross-orthogonality extraction.**  After one coherent commutant gauge,
> extract one coefficient column from each raw branch compressor, prove that
> both columns retain fixed source mass, and prove that their cross inner
> product is `o(1)`.

This target is equivalent to the support-plus-orthogonality part of
`(RPC23)` and is stronger than the one-compressor Hall gate.  Treating two
independent unitary support graphs as the columns of one isometry would
silently assume the theorem to be proved.

## 17. Atomic root characters and the Hellinger gap

There is a second genuinely finite-matrix separator which does not require
choosing blocks of the relative implementer.  Let

\[
 A=U_{13}=\{x_{13}(a):a\in L\}\cong(L,+).
 \tag{RPC59}
\]

For the binary Leavitt coefficient field, `A` is an elementary abelian
`2`-group.  After finite-group exactification on a fixed finite root window,
a matrix model decomposes into character spaces.  Their normalized
multiplicities define a finite atomic probability measure

\[
 \mu_n=\sum_{\chi}m_n(\chi)\,\delta_\chi
 \quad\hbox{on}\quad \widehat A.
 \tag{RPC60}
\]

A gap written directly for all probability measures cannot be correct.  The
canonical exact Leavitt trace restricts to Haar measure on `widehat A`; Haar
is diffuse, invariant under every continuous automorphism of `A`, and gives
the trivial character measure zero.  Thus an inequality of the form

\[
 \sum_{s\in S}\|s_*\mu-\mu\|^2
 \geq \kappa\mu(\widehat A\setminus\{1\})
 \tag{RPC61}
\]

fails if its domain and norm include the invariant Haar measure.  With the
ordinary `ell^2` norm on atomic probability weights it also fails for a
second reason: spreading mass over many atoms makes the norm of the
probability vector tend to zero.

The matrix-specific object is instead the square-root multiplicity vector

\[
 \xi_{\mu_n}(\chi)=\sqrt{m_n(\chi)}.
 \tag{RPC62}
\]

It is a unit vector in the counting-space permutation representation on the
atomic character labels.  The correct candidate inequality is the
Hellinger gap

\[
 \sum_{s\in S}
 \|s\xi_\mu-\xi_\mu\|_2^2
 \geq
 \kappa\bigl(1-\mu(\{1\})\bigr)
 \tag{RPC63}
\]

for every finite atomic `mu`.  Diffuse Haar measure is not a vector in this
counting representation, so the exact tracial Leavitt branch does not
refute `(RPC63)`.  If the label action extends to a property-`(T)` group,
then `(RPC63)` follows once the permutation representation on the
nontrivial character labels has no invariant vector, equivalently once
there is no finite nontrivial character orbit.

Three nonformal gates remain.

1. **Character transport.**  The selected compressor and Steinberg packet
   must define one honest permutation action on a common character-label
   space.  Conjugating one root subgroup to a different root subgroup is not
   yet such an action.
2. **Orbit audit.**  Every nontrivial atomic character orbit for that action
   must be infinite.  One finite orbit destroys `(RPC63)`.
3. **Hellinger control.**  Small normalized-HS covariance defect must imply
   small displacement of the square-root multiplicity vectors.  Trace
   control of finitely many root elements alone gives only weak convergence
   of cylinder marginals and is insufficient.

If these gates hold, `(RPC63)` forces

\[
 \mu_n(\widehat A\setminus\{1\})\longrightarrow0.
 \tag{RPC64}
\]

Every tested nonzero root element then becomes normalized-HS trivial,
contradicting hyperlinear separation.  This is a precise finite-matrix
version of the proposed empirical root-character obstruction.  It avoids
the commutant gauge `(RPC56)`, but it is not yet a proof because the
compressor packet has not been shown to supply gates 1--3.

### 17.1 The Hellinger-control gate is finite and exact

Gate 3 has a dimension-free solution whenever both sides are honest
representations of the same finite abelian group.  Let `rho,sigma` be
unitary representations of a finite abelian group `F` on a `d`-dimensional
space, let `U` be unitary, and let `mu_rho,mu_sigma` be the normalized
character multiplicity distributions.  Put

\[
 \delta^2={1\over |F|}\sum_{a\in F}
 \|U\rho(a)-\sigma(a)U\|_{2,d}^2.
 \tag{RPC65}
\]

If `P_chi,Q_psi` are the two character projections, orthogonality of finite
characters gives

\[
 \delta^2
 =2\sum_{\chi\ne\psi}\|Q_\psi U P_\chi\|_{2,d}^2.
 \tag{RPC66}
\]

The diagonal block mass is therefore `1-delta^2/2`.  Since

\[
 \|Q_\chi U P_\chi\|_{2,d}^2
 \leq\min\{\mu_\rho(\chi),\mu_\sigma(\chi)\},
 \tag{RPC67}
\]

one obtains

\[
 \|\mu_\rho-\mu_\sigma\|_{\rm TV}\leq{\delta^2\over2}
 \quad\hbox{and}\quad
 \sum_\chi
  \bigl(\sqrt{\mu_\rho(\chi)}-
        \sqrt{\mu_\sigma(\chi)}\bigr)^2
 \leq\delta^2.
 \tag{RPC68}
\]

Thus normalized-HS covariance really does control the required Hellinger
displacement after finite-root exactification.

### 17.2 The actual compressor is not a character permutation

The formal compressor identity is

\[
 u\,x_{13}(a)\,u^{-1}=x_{13}(s_0at_0).
 \tag{RPC69}
\]

The coefficient map `alpha_0(a)=s_0 a t_0` is injective and not surjective.
Consequently its dual map on `widehat A` is surjective and generally
many-to-one.  It does not define a permutation representation on the
character labels, so property `(T)` cannot be applied to `(RPC62)` by the
naive argument.  Equation `(RPC68)` only compares `mu_n` with the pushforward
`(alpha_0^*)_*mu_n`.

This is the measure-theoretic form of the balanced extension calculation
`(RPC53)--(RPC54)`: a character on the compressed subtree has freely
choosable signs on the unused subtree.  Reviving the root-character route
therefore requires a uniform transfer-operator theorem for the many-to-one
map `alpha_0^*`, augmented by further atlas relations.  A permutation
spectral gap for the compressor alone is unavailable.

In fact the compressor alone has an explicit nontrivial fixed character.
Use the standard infinite-binary-path representation of the Leavitt
algebra, let

\[
 \zeta=000\cdots,
 \tag{RPC70}
\]

and define the `F_2`-linear functional `ell(a)` to be the coefficient of
`zeta` in `a zeta`.  Prefixing and deleting a leading zero both fix `zeta`,
so

\[
 \ell(s_0at_0)=\ell(a),
 \qquad \ell(1)=1.
 \tag{RPC71}
\]

Therefore

\[
 \chi_0(a)=(-1)^{\ell(a)}
 \tag{RPC72}
\]

is a nontrivial character of `(L,+)` satisfying

\[
 \chi_0\circ\alpha_0=\chi_0.
 \tag{RPC73}
\]

The atomic measure `delta_(chi_0)` is a fixed nontrivial measure for the
dual transfer map.  Hence no positive version of `(RPC63)` can hold using
only the comb compressor.  Any root-character proof must add relations
which move or couple this boundary-path character; merely passing from
probability vectors to square-root multiplicity vectors does not suffice.

### 17.3 Both binary branch compressors still have common fixed characters

Using the second corner map does not repair the transfer gap by itself.
Put

\[
 \alpha_i(a)=s_iat_i,\qquad i=0,1.
 \tag{RPC74}
\]

Every algebraic trace `ell:L->F_2`, meaning an `F_2`-linear map satisfying
`ell(ab)=ell(ba)`, obeys

\[
 \ell(\alpha_i(a))
 =\ell(s_iat_i)
 =\ell(at_is_i)
 =\ell(a)
 \quad(i=0,1).
 \tag{RPC75}
\]

There are nonzero such traces.  One conceptual verification uses the
standard graded universal-trace calculation for the one-vertex two-loop
Leavitt path algebra: in degree one,

\[
 HH_0(L)_1=L_1/[L,L]_1
 \cong
 \mathbf F_2\{s_0,s_1\}/(1-\mathrm{rotation}),
 \tag{RPC76}
\]

and rotation is the identity on length-one loops.  Thus the necklace class
of `s_0`, for example, gives an `F_2`-valued trace with
`ell(s_0)=1`.  Equivalently, compose the universal trace
`L->[L,L]`-coinvariants with the coordinate functional of that necklace
class.

Consequently

\[
 \chi_\ell(a)=(-1)^{\ell(a)}
 \tag{RPC77}
\]

is a nontrivial additive character fixed simultaneously by both dual
transfer maps.  The point mass `delta_(chi_ell)` has zero two-branch
Hellinger energy while assigning full mass to a nontrivial character.
Therefore no version of `(RPC63)` using only the two covariance maps
`alpha_0,alpha_1` can have a positive gap.

This also explains why the elementary calculation with `a=1` is
insufficient.  Simultaneous invariance forces `ell(1)=0` because
`1=s_0t_0+s_1t_1`, but nonzero-degree necklace traces already vanish on
`1`.  A live root-character argument must include relations which destroy
the nonzero graded universal-trace classes, not merely both binary corner
embeddings.

The graded Hochschild-homology calculation used in `(RPC76)` is Theorem
4.4 of Pere Ara and Guillermo Cortinas, *Tensor products of Leavitt path
algebras*, Proc. Amer. Math. Soc. 141 (2013), 2629--2639,
arXiv:1108.0352.  For nonzero degree it identifies `HH_0` with the
cokernel of `1-rotation` on closed paths of that degree.

### 17.4 Even the regular margin at `1` has a four-atom invariant model

The fact that every simultaneously fixed algebraic trace in `(RPC75)` has
`ell(1)=0` does not revive the two-compressor argument.  There is an exact
finite atomic model which is invariant under both dual compressor maps and
already has regular trace on the root element labelled by `1`.

Let

\[
 S=\mathbf Z/3\mathbf Z\sqcup\{*\}.
 \tag{RPC78}
\]

On the three-cycle let `P_0(q)=q+1` and `P_1(q)=q-1`, and fix `*` under
both permutations.  Define an `F_2`-valued output by

\[
 x(0)=x(1)=1,\qquad x(2)=x(*)=0.
 \tag{RPC79}
\]

Then, at every state,

\[
 x(s)=x(P_0s)+x(P_1s).
 \tag{RPC80}
\]

For a binary word `mu`, let `P_mu` be the corresponding composition and
define an additive functional on the diagonal cylinder algebra by

\[
 \ell_s(s_\mu t_\mu)=x(P_\mu s).
 \tag{RPC81}
\]

Set `ell_s(s_mu t_nu)=0` when `mu!=nu` and extend linearly.  Equation
`(RPC80)` is precisely the cylinder-expansion consistency

\[
 \ell_s(s_\mu t_\mu)
 =\ell_s(s_{\mu0}t_{\mu0})+
  \ell_s(s_{\mu1}t_{\mu1}),
 \tag{RPC82}
\]

while off-diagonal expansions remain off diagonal.  Hence `(RPC81)` gives
four well-defined additive functionals on the binary Leavitt algebra.  The
two dual corner maps permute them according to `P_0` and `P_1`.  Therefore

\[
 \mu={1\over4}\sum_{s\in S}\delta_{\chi_s},
 \qquad \chi_s(a)=(-1)^{\ell_s(a)},
 \tag{RPC83}
\]

is an exactly invariant four-atom measure for both compressors.  Since
`ell_s(1)=x(s)`, exactly two atoms take the value `-1` at `1` and two take
the value `+1`.  Thus

\[
 \int\chi(1)\,d\mu(\chi)=0.
 \tag{RPC84}
\]

This is the regular-character margin at the first nonzero root element.
Consequently neither common fixed characters nor the single regular trace
condition at `1` can yield the required Hellinger gap.  A viable atomic
argument must use additional noncentral/Pauli relations and control a
larger regular Fourier window; the two compressor maps alone already admit
the exact finite obstruction `(RPC78)--(RPC84)`.

### 17.5 Exact finite atomic obstructions exist at every diagonal depth

The four-atom model is not a low-depth accident.  At every prescribed
binary depth there is an exactly two-compressor-invariant finite atomic
measure whose Fourier transform is the regular character on the whole
diagonal cylinder window at that depth.

Let `D` be the diagonal cylinder subspace of the binary Leavitt algebra,
with its standard basis projections

\[
 p_\mu=s_\mu t_\mu,
 \qquad
 p_\mu=p_{\mu0}+p_{\mu1}.
 \tag{RPC85}
\]

Fix `r>=1`, let `B_r={0,1}^r`, and put

\[
 W_r=\mathbf F_2^{B_r}.
 \tag{RPC86}
\]

For a word `mu` of length at most `r`, write `v_mu in W_r` for the
indicator of the set of depth-`r` words beginning with `mu`.  Thus the
vectors `v_mu`, `|mu|=r`, are the standard basis, and

\[
 v_\mu=v_{\mu0}+v_{\mu1}.
 \tag{RPC87}
\]

Let `E_r` be the span of the `v_mu` with `|mu|=r-1`.  It has dimension
`2^(r-1)`.  For `i=0,1`, the prescription

\[
 j_i(v_\mu)=v_{i\mu}
 \qquad(|\mu|=r-1)
 \tag{RPC88}
\]

defines an injective linear map `j_i:E_r->W_r`.  Extend it to an
automorphism `A_i in GL(W_r)`.  Such an extension exists by completing a
basis of `E_r` and its image.  If `v=v_emptyset` is the all-one vector,
then `v in E_r` after expansion at depth `r-1`, and `(RPC88)` gives

\[
 A_0v=v_0,
 \qquad A_1v=v_1,
 \qquad v=A_0v+A_1v.
 \tag{RPC89}
\]

More generally, if `mu=mu_1...mu_k` and `k<=r`, then

\[
 A_\mu v:=A_{\mu_1}\cdots A_{\mu_k}v=v_\mu.
 \tag{RPC90}
\]

Indeed the rightmost maps successively create the suffix of `mu`, and each
remaining `A_i` prefixes that suffix; every intermediate proper cylinder
vector lies in `E_r` after expansion to depth `r-1`.

Let the finite state space be the dual vector space `S_r=W_r^*`.  For
`q in S_r`, define an `F_2`-linear functional on the diagonal cylinder
algebra by

\[
 \ell_q(p_\mu)=q(A_\mu v).
 \tag{RPC91}
\]

Equation `(RPC89)` implies

\[
 A_\mu v=A_\mu A_0v+A_\mu A_1v,
 \tag{RPC92}
\]

so `(RPC91)` respects every refinement relation `(RPC85)` and is
well-defined at all depths, including depths beyond `r`.  Put

\[
 \chi_q(a)=(-1)^{\ell_q(a)}.
 \tag{RPC93}
\]

The dual automorphisms

\[
 P_i(q)=q\circ A_i
 \tag{RPC94}
\]

permute `S_r`.  Since `alpha_i(p_mu)=p_(i mu)`, equations
`(RPC90)--(RPC94)` give

\[
 \chi_q\circ\alpha_i=\chi_{P_i(q)}.
 \tag{RPC95}
\]

Consequently the uniform atomic measure

\[
 \nu_r={1\over |S_r|}\sum_{q\in S_r}\delta_{\chi_q}
 \tag{RPC96}
\]

is invariant under both dual compressor maps, exactly rather than
asymptotically.

Finally take a nonzero diagonal element in the depth-`r` window,

\[
 a=\sum_{|\mu|=r}c_\mu p_\mu\ne0.
 \tag{RPC97}
\]

By `(RPC90)`, the vector paired with `q` in `ell_q(a)` is

\[
 \sum_{|\mu|=r}c_\mu A_\mu v
 =\sum_{|\mu|=r}c_\mu v_\mu\ne0,
 \tag{RPC98}
\]

because the depth-`r` cylinder vectors are a basis of `W_r`.  Exactly half
of the functionals `q in W_r^*` take value one on this nonzero vector.
Therefore

\[
 \int\chi(a)\,d\nu_r(\chi)=0
 \qquad
 (0\ne a\in\operatorname{span}\{p_\mu:|\mu|=r\}).
 \tag{RPC99}
\]

Thus `nu_r` has the exact regular Fourier character on the entire
`2^r`-dimensional diagonal root window while having zero two-compressor
Hellinger displacement.  No argument using only the two corner-transfer
maps and any fixed finite collection of diagonal root Fourier marginals can
produce a positive gap: choose `r` large enough to contain that collection
and use `(RPC96)--(RPC99)`.  A live character argument must therefore use
genuinely off-diagonal coefficients or noncentral/Pauli relations.  Merely
increasing the diagonal root depth is now closed.

### 17.6 Local automorphism completion closes every additive-only window

The preceding construction is a special case of a general finite-window
lemma.  It closes not only diagonal cylinders but every argument which uses
finitely many additive-root coefficients and only injective linear
compressor covariance.

**Lemma (finite-window automorphism completion).**  Let `V` be an
`F_2`-vector space, let

\[
 \alpha_1,\ldots,\alpha_m:V\longrightarrow V
 \tag{RPC100}
\]

be injective linear maps, let `K<=V` be finite-dimensional, and fix a word
radius `r>=1`.  There are a finite-dimensional subspace `E<=V`,
automorphisms `A_i in GL(E)`, and a linear projection `pi:V->E` with the
following properties:

1. `K<=E` and every `alpha_w(K)` with `|w|<=r` lies in `E`;
2. if
   \[
    D=\operatorname{span}\{\alpha_w(K):|w|\le r-1\},
    \tag{RPC101}
   \]
   then `A_i a=alpha_i(a)` for every `a in D`;
3. `pi` is the identity on `E`.

**Proof.**  Take

\[
 E=\operatorname{span}\{\alpha_w(K):|w|\le r\}.
 \tag{RPC102}
\]

Each restriction `alpha_i|D:D->alpha_i(D)` is a linear isomorphism between
two subspaces of `E`.  Complete a basis of `D` and its image to bases of
`E`; the resulting basis bijection extends `alpha_i|D` to an automorphism
`A_i` of `E`.  Finally extend a basis of `E` to one of `V` and let `pi` be
the coordinate projection onto `E`.  This proves all three assertions.
\(\square\)

Let `S=E^*`.  For `q in S`, define a global additive character of `V` by

\[
 \chi_q(a)=(-1)^{q(\pi(a))}.
 \tag{RPC103}
\]

The dual automorphisms

\[
 P_i(q)=q\circ A_i
 \tag{RPC104}
\]

permute `S`.  For every `a in D`, `(RPC100)--(RPC104)` give the exact local
covariance identity

\[
 \chi_q(\alpha_i(a))=\chi_{P_i(q)}(a).
 \tag{RPC105}
\]

Moreover the uniform measure

\[
 \nu={1\over|E^*|}\sum_{q\in E^*}\delta_{\chi_q}
 \tag{RPC106}
\]

is invariant under every `P_i`, and for every nonzero `a in E`,

\[
 \int\chi(a)\,d\nu(\chi)=0.
 \tag{RPC107}
\]

The last equality is just orthogonality of the characters of the finite
additive group `E`: a nonzero vector is detected by exactly half of `E^*`.

Apply the lemma to `V=(L,+)` and the corner maps
`alpha_i(a)=s_iat_i`.  On any prescribed finite coefficient window,
`(RPC105)` supplies exact compressor transport while `(RPC107)` supplies
the full regular root character.  The permutations `P_i` can be implemented
by genuine permutation unitaries on `ell^2(E^*)`, so this is an exact finite
matrix model of all additive and covariance data in that window.

Consequently no dimension-free contradiction can use only:

* finite additive root subgroups;
* regular Fourier multiplicities on those subgroups; and
* covariance under finitely many injective linear coefficient maps.

This remains true for arbitrary finite windows and arbitrary finite word
radius.  A successful atlas obstruction must use relations which are not
contained in that linear-covariance language: for example Steinberg
commutators coupling coefficient multiplication, cross-root Pauli blocks,
or the raw second-chart relations which mix such blocks.  This is the exact
reason the next live calculation is noncentral/Pauli coefficient extraction,
not a larger additive Fourier decomposition.

## 18. Three multiplicative relations suffice: no additive extraction is needed

The original coefficient target `(RPC23)` asks for the additive relation

\[
 Y_0X_0+Y_1X_1=I.
 \tag{RPC108}
\]

That is unnecessarily strong.  The cross relation `t_0s_1=0`, together
with the two inverse relations `t_is_i=1`, already has a dimension-free
matrix obstruction.  Crucially, all three are multiplicative coefficient
identities and can in principle be read from Steinberg commutators; no
source of operator addition has to be extracted from a group microstate.

**Lemma (three-product contraction gap).**  Let `T_0,S_0,T_1,S_1` be
contractions in a finite matrix algebra with normalized trace and normalized
Hilbert--Schmidt norm.  Then

\[
 \boxed{
 \max\bigl\{
 \|T_0S_0-I\|_2,
 \|T_1S_1-I\|_2,
 \|T_0S_1\|_2
 \bigr\}\ge 2-\sqrt3>{1\over4}.}
 \tag{RPC109}
\]

**Proof.**  Let the maximum in `(RPC109)` be `epsilon` and suppose
`epsilon<2-sqrt(3)`.  For any two contractions `A,B`, positivity of the two
Gram deficiencies gives

\[
 0\le\operatorname{Re}\operatorname{tr}
 ((I-A^*A)(I-BB^*)),
 \qquad
 \|AB\|_2^2\ge\|A\|_2^2+\|B\|_2^2-1.
 \tag{RPC110}
\]

The two approximate right inverses and normalized-trace Cauchy--Schwarz give

\[
 \begin{aligned}
 1-\varepsilon
 &\le|\operatorname{tr}(T_0S_0)|
 \le\|T_0\|_2\|S_0\|_2\le\|T_0\|_2,\\
 1-\varepsilon
 &\le|\operatorname{tr}(T_1S_1)|
 \le\|T_1\|_2\|S_1\|_2\le\|S_1\|_2.
 \end{aligned}
 \tag{RPC111}
\]

Apply `(RPC110)` to `A=T_0` and `B=S_1`.  Then

\[
 \varepsilon^2\ge\|T_0S_1\|_2^2
 \ge2(1-\varepsilon)^2-1.
 \tag{RPC112}
\]

Equivalently,

\[
 \varepsilon^2-4\varepsilon+1\le0.
 \tag{RPC113}
\]

The smaller root is `2-sqrt(3)` and the larger root exceeds one.  This
contradicts the assumption and proves `(RPC109)`.  The complete finite-matrix
argument, including the operator-norm-to-Hilbert--Schmidt multiplication
bound and positivity calculation, is formalized in
`GroupApproximation/Sofic/LeavittTraceFloor.lean` as
`two_sub_sqrt_three_le_of_leavitt_product_defects`; its rational corollary is
`one_fourth_le_of_leavitt_product_defects`. \(\square\)

This replaces `(RPC23)` by the strictly smaller extraction target:

> **Multiplicative Pauli-coefficient extraction.**  From a canonical
> regular-margin atlas microstate of defect `delta`, extract four
> contractions `T_0,S_0,T_1,S_1` in one finite multiplicity corner such
> that
> \[
>  \max\{\|T_0S_0-I\|_2,\|T_1S_1-I\|_2,
>          \|T_0S_1\|_2\}
>  \le C\delta^c
>  \tag{RPC116}
> \]
> with `C,c>0` independent of the multiplicity.

Equations `(RPC109)` and `(RPC116)` give the uniform atlas defect floor

\[
 \delta\ge\left({2-\sqrt3\over C}\right)^{1/c}.
 \tag{RPC117}
\]

The three target identities are precisely

\[
 t_0s_0=1,
 \qquad t_1s_1=1,
 \qquad t_0s_1=0.
 \tag{RPC118}
\]

At the group level their products occur in the fixed Steinberg packet

\[
 [x_{12}(t_i),x_{23}(s_j)]=x_{13}(t_is_j),
 \tag{RPC119}
\]

so the two inverse cases land in `x_13(1)` and the cross case is the
identity.  These commutator relations alone only encode the finite
Heisenberg pairing and do not yet manufacture the coefficient contractions;
compressor covariance and Pauli block disintegration are still required.
But the former additivity gate is gone: once those four contraction blocks
are identified, no reconstruction of `s_0t_0+s_1t_1=1`, no partial trace
implementing a sum, and no full Leavitt family is necessary.

The sharp next theorem is therefore `(RPC116)`, derived from the raw
compressor and adjacent-root relations in one coherent Pauli gauge.  This is
strictly weaker than `(RPC23)`, `(RPC23a)`, cross-orthogonality of two full
columns, or the four-step flag theorem `(RPC42)`.

## 19. The multiplicative commutator packet has an exact regular Pauli model

The fact that `(RPC119)` mentions all three desired coefficient products
does not by itself make it a coefficient extraction.  There is an exact
finite model which gives the complete packet its regular trace and in which
the products are only Weyl commutation signs.

Let `E` be the extraspecial two-qubit group

\[
 \begin{split}
 E=\langle X_0,X_1,Z_0,Z_1,c\mid {}&c^2=X_i^2=Z_j^2=1,
 \quad c\text{ central},\\
 &[X_i,X_j]=[Z_i,Z_j]=1,
 \quad [X_i,Z_j]=c^{\delta_{ij}}\rangle .
 \end{split}
 \tag{RPC120}
\]

It has order `32`.  In its left regular representation put

\[
 x_{12}(t_i)\longmapsto\lambda_E(X_i),\qquad
 x_{23}(s_j)\longmapsto\lambda_E(Z_j),\qquad
 x_{13}(1)\longmapsto\lambda_E(c),\qquad
 x_{13}(0)\longmapsto I.
 \tag{RPC121}
\]

Then every relation in `(RPC119)` is exact:

\[
 [\lambda_E(X_i),\lambda_E(Z_j)]
   =\lambda_E(c)^{\delta_{ij}}.
 \tag{RPC122}
\]

Moreover the normalized trace of `lambda_E(g)` is zero for every
`g!=1`.  Thus `(RPC121)` has the strongest possible finite regular margin;
it is not a low-trace or trivial-sector escape.

The representation-theoretic meaning is transparent.  On the `c=-1`
sector, the regular representation is

\[
 \mathbf C^4\otimes\mathbf C^4,
 \tag{RPC123}
\]

with `X_0,X_1,Z_0,Z_1` acting as the standard two-qubit Pauli matrices on
the first factor and trivially on the multiplicity factor.  The equations
`t_is_j=delta_ij` have therefore become a nondegenerate symplectic pairing
of four labels, not products of four operators on the second factor.  In
particular, no basis-free operation using only `(RPC119)` can produce the
four contractions in `(RPC116)`: applying it to `(RPC121)` would contradict
the exact gap `(RPC109)`.

This gives a stricter stopping rule than the qualification after
`(RPC119)`.  A successful extraction proof must exhibit a named relation
involving a raw compressor (or an equivalent cross-chart word) whose Pauli
block action is **not** already an automorphism of the finite symplectic
label space `(RPC120)`.  Adding Clifford normalizers of `(RPC120)` does not
help: the semidirect product of `E` by any finite group of symplectic label
automorphisms again supplies an exact finite regular model.

There is also a precise fiber mismatch behind this countermodel.  For an
additive functional `ell:R->F_2`, let

\[
 \ell_i(a)=\ell(s_iat_i).
 \tag{RPC124}
\]

The dual map `ell |-> ell_i` is many-to-one because the corner map is
injective and proper.  Compressor covariance therefore relates the source
spectral data at `ell_i` to the direct sum of all target fibers extending it;
it does not canonically carry one target fiber `ell` onto one source fiber.
Algebraically, right multiplication by the Leavitt generators acts on the
infinite radical quotient `V_ell` from `(RPC29)`.  A finite Pauli truncation
sees only arrows among the extension fibers, however.  The identities
`t_is_j=delta_ij` compose their Weyl signs correctly, but do not turn the
arrows into four endomorphisms of one finite multiplicity space.  That
identification is exactly what `(RPC116)` needs.

Consequently the remaining analytic statement can be sharpened once more:

> **Fiber-identification gate.**  Use a fixed raw-compressor/adjacent-root
> packet to resolve, with dimension-independent normalized-Hilbert--Schmidt
> loss, the extension fibers of the two proper dual maps
> `ell |-> ell_0,ell_1`, in a way which carries the four radical-quotient
> arrows to contractions on one finite tracial multiplicity algebra.

After this gate, `(RPC118)` gives `(RPC116)` and `(RPC109)` finishes the
argument.  Before this gate, the exact regular model `(RPC120)--(RPC123)`
shows that the Steinberg commutators contain no hidden matrix-product
contradiction.

## 20. The correct invariant is a pair of radical quotients

There is now a direct robust alternative to the Fourier formulation below.
`TRUE_ROBUST_PAIRED_QUOTIENT_HAMMING_FLOOR.md` proves that finite perfect
binary labels already have a universal `1/36` error floor for the two
diagonal transports and one crossed-zero transport.  Collision counting
automatically repairs the relevant diagonal label maps to permutations.
Consequently the complex Fourier unitary, its two trivial modes, and the
near-bijectivity estimates are not separate obligations if the microstate
argument extracts a uniform finite perfect-pairing label model.  The older
Fourier formulation remains a fallback when only operator blocks, rather
than labels, can be recovered.

The finite contradiction in this section is independently formalized in
`GroupApproximation/Leavitt/FinitePairedQuotientObstruction.lean`; see
`TRUE_FINITE_PAIRED_QUOTIENT_OBSTRUCTION.md`.  The formal statement is
basis-free and needs only point separation, the two diagonal transports, and
one crossed-zero transport.  Accordingly none of the remaining work is in
the finite algebraic endpoint: it is entirely in robust extraction of those
data from common Hilbert--Schmidt matrix coordinates.

There is a basis-free algebraic form of the four missing arrows.  For an
additive functional `ell:R->F_2`, retain the bilinear form

\[
 b_\ell(a,b)=\ell(ab)
 \tag{RPC125}
\]

and define its two radicals

\[
 L_\ell=\{a:b_\ell(a,R)=0\},\qquad
 R_\ell=\{b:b_\ell(R,b)=0\}.
 \tag{RPC126}
\]

The left radical is a right ideal and the right radical is a left ideal.
Consequently right multiplication by `t_i` descends to
`V_ell=R/L_ell`, while left multiplication by `s_j` descends to
`W_ell=R/R_ell`.  The multiplicative Leavitt relations give the exact
biorthogonality identity

\[
 b_\ell(a t_i,s_j b)
   =\ell(a(t_i s_j)b)
   =\delta_{ij}b_\ell(a,b).
 \tag{RPC127}
\]

This gives a shorter proof of the infinite-rank statement `(RPC27)`, using
only the multiplicative relations.  If `(RPC125)` had finite nonzero rank,
the induced pairing `V_ell x W_ell->F_2` would be nondegenerate between two
finite spaces of the same dimension.  The diagonal cases of `(RPC127)` make
right multiplication by `t_0` on `V_ell` and left multiplication by `s_1`
on `W_ell` injective, hence bijective.  The cross case then makes the pairing
zero: for arbitrary `x,y`, write `x=a t_0` and `y=s_1b`, and obtain
`b_ell(x,y)=0`.  This contradicts nondegeneracy (and `ell(1)=1`).

The analytic endpoint should therefore not be phrased as recovering ring
elements from arbitrary blocks.  There is one further Fourier qualification.
If `V,W` are finite `F_2`-spaces with a perfect pairing `b`, the matrix of
`b` in linear bases is invertible over `F_2`, but it is **not** a complex
unitary.  The canonical complex unitary is the normalized Fourier transform

\[
 (\mathcal F_b)_{v,w}=|V|^{-1/2}(-1)^{b(v,w)}
 \quad(v\in V,w\in W).
 \tag{RPC127a}
\]

For linear arrows `R,L`, the identity `b(Rv,Lw)=b(v,w)` becomes the desired
intertwining identity for their permutation operators.  But
`b(Rv,Lw)=0` gives the constant Fourier kernel, a rank-one operator, rather
than zero.  It vanishes only after deleting the trivial mode: on the source
remove the constant vector, and on the target remove the delta mass at zero.
The Fourier transform restricts to a unitary between these two codimension-one
spaces, which are invariant under permutation operators induced by bijective
linear arrows.

This exact observation introduces two analytic obligations.  Approximate
arrows must be made near-bijective before their pullback operators are
contractions for uniform counting measure, and the two trivial modes must be
removed with asymptotically invariant projections.  Algebraic
nondegeneracy supplies neither assertion quantitatively.

> **Robust radical-quotient gate.**  From a canonical regular-margin atlas
> microstate, construct equally dimensional, canonically traced finite
> multiplicity spaces `V_n,W_n`, contractions `R_i` on `V_n` and `L_j` on
> `W_n`, and a reduced Fourier unitary `U_n:W_n->V_n` such that
> \[
>  \|R_0^*U_nL_0-U_n\|_2,
>  \quad \|R_1^*U_nL_1-U_n\|_2,
>  \quad \|R_0^*U_nL_1\|_2
>  \le C\delta^c.
>  \tag{RPC128}
> \]

Right multiplication in `(RPC128)` by `U_n^*` preserves normalized
Hilbert--Schmidt norm.  Thus

\[
 T_i=R_i^*,\qquad S_j=U_nL_jU_n^*
 \tag{RPC129}
\]

are contractions satisfying `(RPC116)`, and
`two_sub_sqrt_three_le_max_leavitt_product_hsNorm` supplies the uniform gap.

Here `V_n,W_n` denote the reduced complex Fourier spaces, not the original
`F_2` radical quotients.  The word **unitary** in this gate is essential.  An arbitrary invertible, or
merely ``quantitatively nondegenerate'', pairing matrix `J_n` does not give a
dimension-free reduction: conjugation by `J_n` magnifies errors by its
condition number, which can diverge with the microstate dimension.  A
singular-value truncation is an acceptable alternative only if one proves
all three missing estimates: a uniform lower singular-value bound on the
retained sector, asymptotic invariance of that sector under all four arrows,
and positive normalized tracial mass of the sector.  None of those estimates
follows from algebraic nondegeneracy alone.  In the expected Pauli
disintegration the normalized Fourier pairing is unitary, so the live task is
to show that the raw compressor preserves the reduced flat pairing while
resolving its extension fibers, makes the induced arrows near-bijective, and
controls leakage through the two removed trivial modes.  This corrected
formulation is gauge-invariant and does not hide a condition-number or
rank-one-mode assumption.

It also pinpoints why the finite Pauli model `(RPC120)` is harmless.  That
model realizes one nondegenerate pairing table, but it contains no
well-defined endomorphisms induced simultaneously by the four coefficient
multiplications.  The raw compressor identities must manufacture precisely
those quotient arrows and control leakage through the finite radicals.  No
additional additive relation is needed.
