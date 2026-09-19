# A unique trace and complete matrix stability above size one

Date: 5 September 2026. Complete proof, independently internally reviewed.
The unitary-group agent checked the Stiefel connectivity and numerical
range, local polar lift, natural matrix maps, relative homotopy continuity,
trace contraction, and trace pairing. No gap was found. No external
verification or publication-priority claim is made.

The same reviewer subsequently checked the original Nistor scan and
the stable-rank-two deduction in Section 5. Native Cairn
`check --changed` and `preview` both passed on MSI for the 73-node
closure (38 claims and 35 routes) containing this theorem. These
structural checks do not formally verify the mathematics.

This strengthens the [finite-abelian LIX construction](stw59-exact-finite-abelian-component-groups-2026-09-05.md).
It applies also to the original order-two and factorial towers.
It does not resolve an additional named open problem.

## 1. Statement

For each nonzero finite abelian group G, let A=A_G be the already
constructed simple unital AH algebra with K1(A)=0 and
U(A)/U0(A)=G. Write its system as

    A_i = Gamma(X_i, End(E_i)),
    rank(E_i) = r_i = R 2^i,       dim(X_i) = 2 r_i,
    E_(i+1) = pi_i^* E_i direct-sum (E_i(x_i) tensor L_(i+1)),
    phi_i(a) = pi_i^*a direct-sum (a(x_i) tensor 1_L).

The bases X_i are connected finite CW complexes. Both blocks in phi_i
have rank r_i, and the maps are injective and unital.

**Theorem.** This algebra has stable rank exactly two and a unique
tracial state tau. Its trace
pairing has range

    tau_*(K0(A)) = (1/R) Z[1/2].

For every m>=2 and every integer k>=0, the canonical stable map is an
isomorphism

    pi_k U(M_m(A)) --> K_(k+1)(A).

Here pi_0 denotes the component group, and higher homotopy groups are
based at the identity. In particular, M_m(A) is K-stable for every
m>=2, and all its unitary groups are connected. Thus A is a full
unital corner of the unital simple K-stable algebra M2(A), although
A itself is not K1-injective when G is nonzero.

The superscript-free notation K_(k+1) uses the usual two-periodic
C*-algebra K-theory. No assertion about the higher unstable kernels
of U(A) is made.

## 2. The trace contracts explicitly

For a in A_i let

    f_a(x) = Tr(a(x))/r_i.

Every tracial state on A_i is integration of f_a against a probability
measure on X_i. This can be seen without trivializing E_i globally:
on a trivializing neighborhood, the trace vanishes on off-diagonal
matrix entries and has identical restrictions on the diagonal entries.
A partition of unity reduces to these neighborhoods. Its restriction
to the scalar center supplies the probability measure, and these local
identities determine its value on every section.

Because the two summands have the same rank,

    f_(phi_i(a)) = (f_a o pi_i + f_a(x_i))/2.                 (2.1)

For j>i, iteration gives

    f_(phi_(i,j)(a)) = 2^(-(j-i)) f_a o pi_(i,j) + c_(i,j)(a) 1,

where c_(i,j)(a) is a scalar independent of the point of X_j. For
two tracial states sigma and tau on the limit this implies

    |sigma(a)-tau(a)| <= 2^(1-(j-i)) ||a||.

Letting j tend to infinity shows equality on every stage and hence
on A. Existence of a trace was proved in the original construction
by compactness of the inverse system of tracial state spaces. Thus
there is exactly one trace; simplicity makes it faithful.

Under the Morita identification K0(A_i)=K^0(X_i), a virtual bundle
of rank s has trace s/r_i. Connectedness of X_i makes its rank a
single integer, independent of the trace measure. Conversely every
integer rank occurs in K^0(X_i), for instance as a virtual sum of
trivial lines. Therefore the stage trace image is exactly (1/r_i) Z.
Every K0 class of the inductive limit comes from a stage, and unitality
preserves the trace pairing. Taking the union proves the stated range.
This computes a trace image, not the ordered K0 group.

## 3. A finite-bundle stable range

**Lemma.** Let X be a finite CW complex of dimension d, and let F be
a complex vector bundle of constant positive rank r. If

    d+k+1 <= 2r,                                             (3.1)

then the canonical stable map

    pi_k U(Gamma(X,End(F))) --> K_(k+1)(Gamma(X,End(F)))

is an isomorphism.

**Proof.** We give the argument for bundle stabilizations so no trivial
matrix presentation of End(F) is assumed. For any positive-rank complex
bundle H over X, let S(H,F+H) be the space of fiberwise isometric
embeddings of H into F direct-sum H, based at the standard inclusion.
Its fiber is the complex Stiefel manifold

    V_s(C^(r+s)) = U(r+s)/U(r),       s=rank(H).

This fiber is 2r-connected. Indeed forgetting vectors one at a time
gives sphere fibrations; their smallest sphere is S^(2r+1), and the
homotopy exact sequences prove vanishing through degree 2r.

Relative cellular obstruction theory now makes S(H,F+H)
(2r-d)-connected whenever 2r>=d. A j-sphere of sections extends
over a (j+1)-disk because the extension problem on
X times D^(j+1) has dimension d+j+1<=2r+1. Every obstructing
fiber homotopy group is therefore zero. The same argument for j=0
joins any section to the standard inclusion.

The gauge group G(F+H) acts transitively on this section space,
and the stabilizer of the standard inclusion is G(F). Here is the
local lifting needed for this assertion. For uniformly close
isometric embeddings v,w, put P=vv*, Q=ww*, and

    T = wv* + (1-Q)(1-P).

This is an invertible endomorphism of F+H when v,w are sufficiently
close. It maps v exactly to w and satisfies T*T v=v. Its polar
unitary therefore maps v to w, depends continuously on the close
pair, and equals 1 for v=w. Lifting a path of sections by finitely
many such charts proves transitivity. The charts also give the
locally trivial principal bundle

    G(F) --> G(F+H) --> S(H,F+H).

Its homotopy exact sequence proves that G(F)-->G(F+H) induces
an isomorphism on pi_k under (3.1): both pi_k and pi_(k+1) of
the section space vanish. For k=0 this is the corresponding
component-group assertion using connectivity and simple connectivity
of the section space.

Apply this with F replaced successively by nF and H=F. Inequality
(3.1) continues to hold as n increases. Thus every map

    pi_k G(nF) --> pi_k G((n+1)F)

is an isomorphism. Since G(nF)=U(M_n(Gamma End(F))), the algebraic
direct limit of these homotopy groups is the stable K-group by the
definition of K1 and Bott periodicity. This proves the lemma for
the canonical stable map, not merely an abstract group isomorphism.
Square.

The Stiefel sphere fibrations and Bott identification are the same
standard bundle inputs used in Sections 2--3 of the
[exact factorial proof](stw59-exact-factorial-component-groups-2026-09-05.md).
For background on relative cellular obstruction theory and complex
bundles, see [Hatcher, Vector Bundles and K-Theory](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf).
The proof above supplies the required numerical range explicitly.

## 4. Passing the range to the limit

Fix m>=2 and k>=0. At stage i the algebra M_m(A_i) has bundle
E_i^(direct-sum m), of rank m r_i over a base of dimension 2r_i.
The lemma applies as soon as

    k+1 <= 2(m-1) r_i.                                      (4.1)

Since r_i=R 2^i, this holds for every sufficiently large i. Consequently
the canonical stable maps

    pi_k U(M_m(A_i)) --> K_(k+1)(A_i)

are isomorphisms on a tail. Matrix Morita identification is used on
the right; the square with every phi_i commutes by naturality.

For completeness, homotopy groups commute with the present injective
unital inductive limits. A continuous map from a compact sphere into
U(M_m(A)) has a uniformly close approximation in one stage: take a
finite partition of unity and stage approximations to its values.
Polar decomposition makes this approximation unitary. Uniformly close
unitaries are homotopic by their relative principal logarithm.
To preserve a basepoint, multiply the approximation by the inverse of
its value there; the error remains arbitrarily small.

Null-homotopies are detected similarly using a disk. Approximate the
disk map in one stage, including the stage of its prescribed boundary.
For the difference on the boundary, a bounded linear extension into
continuous functions on the disk exists: extend radially on an outer
collar and taper it to zero on the inner disk. Subtract this extension
before taking the polar part. This keeps the boundary exact and the
uniform error small, so the polar map is a disk of stage unitaries
with exactly the prescribed boundary. The same argument with interval
endpoints proves the component-group statement. It proves both
surjectivity and injectivity of the homotopy direct-limit map.

K-theory is also continuous. Taking direct limits of the tail
isomorphisms therefore proves the theorem. The stable maps for every
m>=2 are canonical, so every consecutive inclusion at these sizes
induces isomorphisms in all degrees. In particular the consecutive
matrix maps for M_m(A), whose underlying sizes are m,2m,3m,...,
have this property: M_m(A) is K-stable.

Finally, p=diag(1_A,0) is a full projection in M2(A), and pM2(A)p=A.
For nonzero G its unitary component group is G while K1(A)=0.
This proves the full-corner assertion with both algebras unital and
simple. It does not invoke any general hereditary permanence for
K-stability.

## 5. Stable rank is exactly two

Nistor's Theorem 7(a), printed page 371 of
[Stable rank for a certain class of type I C*-algebras](https://jot.theta.ro/jot/archive/1987-017-002/1987-017-002-015.pdf),
J. Operator Theory 17 (1987), 365--373, computes stable rank for
separable locally trivial homogeneous algebras. For a degree-r
homogeneous algebra over a base of dimension 2r, its formula gives
stable rank two. It applies to each A_i: End(E_i) is locally trivial
and its spectrum is X_i. The original scanned theorem was rendered
on MSI and visually checked; twisting does not violate its hypotheses.

Thus sr(A_i)=2. To pass the upper bound to A, approximate any pair
of elements in A by a pair in one A_i, then approximate that pair
by (a,b) with a*a+b*b invertible in A_i. The same positive element
is invertible in A because the maps are unital. Hence generating
pairs are dense and sr(A)<=2. Stable rank one implies K1-injectivity
by Rieffel's theorem, whereas the nonzero group G lies in the kernel
of the canonical K1 map of A. Therefore sr(A)=2.

## 6. Relation to published stability results

[Seth, Tensorial Permanence of K-Stability for Diagonal AH-Algebras](https://arxiv.org/html/2512.04780v2)
uses full matrix building blocks and scalar diagonal eigenvalue maps
in Definition 2.1. The line-twisted tower here is not asserted to
satisfy that definition. Our matrix-stability conclusion instead
follows from the explicit increasing surplus in (4.1). Seth's
definition and background permanence discussion do not supply a
descent of K-stability from M2(A) to the full corner A.

These deductions sharpen the constructed LIX examples; the named
problem count remains unchanged. Purity is not asserted for A.
Its unique trace does not put it under hypotheses requiring stable
rank one: the calculation above gives stable rank exactly two.
