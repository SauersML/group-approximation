# Persistent Euler coordinates compute the degree-one stabilization cokernel

Date: 5 September 2026. Complete argument independently reviewed
internally. This refines the reviewed simple AH construction;
it is not a claim to solve another named problem.

## 1. Statement

Choose a finite list of integers d_1,...,d_s>=1, with s>=1, and set

    G = direct sum_alpha Z/d_alpha,
    R = max(2,d_1,...,d_s).

There is a simple unital separable nuclear stably finite AH algebra
A=A_(d_1,...,d_s) with a unique trace such that

    K1(A)=0,                  U(A)/U0(A)=G,
    coker(pi_1 U(A) -> K0(A)) = Z^s.                    (1.1)

The last map is the canonical stabilization map, with Bott periodicity
identifying its target. More precisely, there is a natural surjection

    Lambda : K0(A) -> direct sum_alpha d_alpha Z

and the sequence

    pi_1 U(A) -> K0(A) --Lambda--> direct sum_alpha d_alpha Z -> 0
                                                               (1.2)

is exact. All pi_1 groups are based at the identity. No injectivity
of the first arrow is asserted.

Every M_m(A), m>=2, is K-stable. Therefore the cokernel in (1.1)
also equals the cokernel of pi_1 U(A)->pi_1 U(M_2(A)). Tensoring
this cokernel with Q gives Q^s, so A is not rationally K-stable.
Its stable rank is exactly two for every s>=1.

Allowing d_alpha=1 makes the degree-one obstruction independently
enlargeable while preserving G. In particular, for every s>=1 there
is such a simple monotracial AH algebra with K1-bijective scalar
unitary group and degree-one stabilization cokernel Z^s: take every
d_alpha=1. These examples also have stable rank exactly two.

## 2. The finite-stage exact sequence

Use the gauge calculation proved in Sections 2--4 of
[the exact factorial proof](stw59-exact-factorial-component-groups-2026-09-05.md)
and Section 2 of
[the finite-abelian proof](stw59-exact-finite-abelian-component-groups-2026-09-05.md).
For a connected finite CW complex X of dimension 2r with K^1(X)=0
and a rank-r complex vector bundle E, put F=E+1. The gauge fibration

    G(E) -> G(F) -> S(F)

has pi_1 G(F)=K^0(X), pi_0 G(F)=0, and
pi_1 S(F)=H^(2r)(X;Z). Its exact sequence consequently gives

    im(pi_1 G(E) -> K^0(X)) = ker Lambda_E.             (2.1)

The arrow from pi_1 G(E) is its canonical stable map. Although
E+1 is not generally a matrix multiple of E, the complement-and-
rotation argument identifies this stabilization with the usual
matrix stabilization under Morita equivalence.

The integral Euler homomorphism Lambda_E is computed in rational
cohomology by

    Lambda_E(beta)
      = sum_(j=0)^r (-1)^(r-j) (r-j)! c_j(E) ch_(r-j)(beta).
                                                               (2.2)

Whenever H^(2r)(X;Z) is torsion free, this formula determines the
integral homomorphism uniquely. This is the same Euler map which
previously computed pi_0 G(E) as its cokernel. Here we retain its
kernel to compute the image of the degree-one stable map.

## 3. The tower, including trivial component coordinates

Let e_alpha=R-d_alpha and form the connected joined base

    M_alpha = S^2 x CP^(d_alpha-1) x CP^(e_alpha),
    E_alpha = 1^(d_alpha) + L_alpha^(e_alpha),
    X_0 = wedge_alpha M_alpha.

Glue the rank-R bundles at their basepoint fibers, matching one
trivial line in every arm. Call the resulting bundle E_0. It has
a global trivial line. This construction is valid also for d_alpha=1:
then CP^0 is a point and the first summand is just one trivial line.
There is no need for two globally trivial lines.

Set r_i=R 2^i and

    X_i = X_0 x product_(j<i) CP^(r_j),
    E_i = pull(E_0) + sum_(j<i) L_(j+1)^(r_j),
    A_i = Gamma(X_i,End(E_i)).

These have dim(X_i)=2r_i, rank(E_i)=r_i, K^1(X_i)=0, and

    H^(2r_i)(X_i;Z) = Z^s.

Every E_i retains its trivial line, so c_(r_i)(E_i)=0. Choose
evaluation points with dense projected tails and use the unital maps

    phi_i(a) = pull(a) + (a(x_i) tensor 1_(L_(i+1))).    (3.1)

Let A be their injective inductive limit.

The finite-stage Euler-image calculation remains valid for every
d_alpha>=1. On each arm its coefficients are integral multiples
of d_alpha. The rank-zero class equal to the S^2 Bott class times
the tautological line on CP^(d_alpha-1), extended by zero to the
other arms, attains +/-d_alpha. For d_alpha=1 the tautological
line on CP^0 is trivial, and this assertion gives +/-1. Hence

    im Lambda_(E_i) = direct sum_alpha d_alpha Z,        (3.2)
    pi_0 U(A_i) = direct sum_alpha Z/d_alpha.

The relative Euler product argument in the finite-abelian proof
shows that adjoining L^(r_i) preserves all these component
coordinates. Point evaluation of a fixed unitary contracts in the
finite matrix group, so (3.1) induces the same component map.
This proves the claimed limit component group, including the zero
coordinates d_alpha=1.

For d_alpha>=2, the earlier characteristic unitary supported on its
arm still gives the generator. Its first matrix contraction needs
only one trivial line from the second copy of E_0; that line exists
in the present construction. Coordinates with d_alpha=1 require
no generator.

## 4. The Euler map survives the actual connecting homomorphism

Under Morita equivalence K0(A_i)=K^0(X_i), the actual map (3.1)
sends a virtual bundle beta of constant virtual rank n to

    beta' = pull(beta) + n[L] in K^0(X_i x CP^r),        (4.1)

where r=r_i. The formula applies to differences of bundles as well:
the evaluation summand depends precisely on virtual rank. Also

    E' = pull(E) + L^r,
    c(E') = pull(c(E))(1+y)^r,       y=c1(L).

Consider the component of Lambda_(E')(pull beta) in old degree 2r
and new degree 2r. In (2.2), ch(pull beta) contributes no new
cohomological degree. Thus the new top degree must come entirely
from the coefficient y^r of (1+y)^r, whose coefficient is one.
The old-degree expression left over is exactly Lambda_E(beta):

    Lambda_(E')(pull beta) = Lambda_E(beta) y^r.         (4.2)

For the other summand n[L], its Chern character is n exp(y).
Every old-degree contribution must therefore come from c(E).
To reach old degree 2r it must contain c_r(E), which is zero
because E has a trivial line. Consequently

    Lambda_(E')(n[L])=0,
    Lambda_(E')(beta')=Lambda_E(beta) y^r.               (4.3)

These are integral equalities: the relevant top cohomology groups
are free abelian, so their rational computations detect equality.
Choose the product orientations consistently so integration of
y^r is one. Under the identifications with Z^s, (4.3) says that
the actual K0 connecting maps preserve every Euler coordinate.

This step is distinct from the component-group transport argument.
There is no assertion that a gauge-loop evaluation block contracts
uniformly over the loop parameter; it need not. Instead (4.1)--(4.3)
compute that block's contribution to the Euler map directly.

## 5. Passage to the limit and the exact cokernel

The maps Lambda_(E_i) therefore induce a homomorphism

    Lambda: K0(A) -> Z^s

whose image is exactly the fixed subgroup in (3.2). The image of
pi_1 U(A) is contained in ker Lambda by (2.1) and naturality.

For the reverse inclusion let x in K0(A) satisfy Lambda(x)=0.
It is represented by beta in K0(A_i) at a finite stage. Formula
(4.3) gives Lambda_(E_i)(beta)=0. By (2.1), beta is the stable
class of an actual based loop in U(A_i); its image is a loop in
U(A) with stable class x. This proves exactness in (1.2).

For the first inclusion one may equivalently use continuity of
nonstable homotopy groups for injective unital inductive limits:
a compactly parameterized loop is uniformly approximated at a
finite stage, polar correction preserves it as a unitary loop,
and a relative approximation on a null-homotopy detects relations.
The identity basepoint is kept exact throughout. This is the
relative continuity argument already checked in
[the matrix-stability proof](stw59-unique-trace-and-matrix-stability-2026-09-05.md).

The first isomorphism theorem now gives

    K0(A)/im(pi_1 U(A)) = direct sum_alpha d_alpha Z = Z^s.

In particular this image is a direct summand of the abelian group
K0(A), since the quotient is free. This splitting is not asserted
to preserve order or to be canonical.

Tensoring the exact sequence with Q preserves exactness and leaves
cokernel Q^s. Thus even the rational degree-one stable map fails
surjectivity, although the finite component group disappears after
rationalization. No calculation of the degree-one kernel is used.

## 6. Structural properties and scope

The density argument, trace contraction, and matrix stable-range
proofs for the earlier towers depend only on connectedness of the
bases, rank r_i, dimension 2r_i, injectivity, and the equal ranks of
the two blocks. They apply unchanged to the present d_alpha=1 arms.
They give simplicity, nuclearity, a unique faithful trace, stable
finiteness, K1(A)=0, trace range (1/R)Z[1/2], stable rank at most
two, and K-stability of every M_m(A) for m>=2.

Stable rank one would force pi_1 U(A)->K0(A) to be surjective,
contradicting (1.1). The required prior-art consequence is proved
in Section 2 of the
[degree-one source audit](stw58-degree-one-primary-citation-audit-2026-09-05.md):
sr(A)=1 gives csr(C(T,A))<=2, so every circle map into each
left-unimodular tuple space Lg_n(A), n>=2, is null-homotopic.
The last-column fibration then makes every adjacent matrix map
surjective on pi_1. Polar deformation and finite stable loop
representatives give the asserted stable surjectivity. This uses
only the verified surjectivity consequence, not the stronger
degree-one injectivity assertion discussed in that audit. The
underlying bound and loop argument are used in Gong--Lin--Xue,
*Determinant rank of C*-algebras*, Theorem 3.10 and Corollary 3.11
([primary paper](https://msp.org/pjm/2015/274-2/pjm-v274-n2-p06-p.pdf)).
Hence sr(A)=2 even when G=0.

For a fixed finite abelian G, choose any decomposition into cyclic
factors of orders at least two, then append any number of factors
of order one. This preserves G and increases the rank of the
degree-one cokernel by exactly that number. When G=0, taking s
order-one arms gives K1-bijective examples with arbitrary positive
degree-one cokernel rank.

This strengthens the known internal LIX examples and pinpoints
their failure of higher stabilization. It does not settle LVIII:
no pureness is asserted for these AH algebras. It makes no claim
of external verification or publication priority.

## 7. Independent review record

Pascal checked the actual Morita connecting map, with no missing
matrix-rank factor, the two separate Euler contributions, integral
cohomology, exactness through the limit, and the free cokernel.
Ohm separately checked the order-one arm extension, the sufficiency
of one global trivial line, the independent Bott attaining classes,
component transport, and the retained structural and matrix-stability
proofs. Ohm also checked that the verified degree-one surjectivity
consequence of stable rank one makes the stable rank exactly two
even for K1-bijective examples. No gap was found in these checks.
