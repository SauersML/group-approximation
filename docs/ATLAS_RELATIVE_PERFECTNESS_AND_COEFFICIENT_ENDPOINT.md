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
