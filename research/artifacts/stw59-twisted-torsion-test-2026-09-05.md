# STW LIX: the diagonal obstruction and the first twisted test

Date: 2026-09-05. Status: proved finite-stage reductions, subsequently
extended to a complete counterexample in
stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md.
No novelty is asserted for the elementary homotopy arguments below.

## 1. Correct the proposed construction class

The claim that no literature result obstructs unstable torsion in a simple
coordinate-diagonal AH limit is incorrect. Seth's Theorem A and Corollary
3.10 show that a simple unital infinite-dimensional diagonal AH algebra
is K-stable even after minimal tensor product with an arbitrary C*-algebra.
In particular it is K1-injective. The definition uses full matrix bundles
and globally diagonal eigenvalue maps; it does not cover arbitrary twisted
homogeneous corners. The earlier stable-rank-one theorem of
Elliott--Ho--Toms already implies K1-injectivity in the simple diagonal
class. Source: [Seth, arXiv:2512.04780v1](https://arxiv.org/html/2512.04780v1),
Definition 2.1, Theorem A, and Corollary 3.10.

Here is a direct finite-stage explanation of the relevant injectivity
mechanism. Let u in U(M_r(C(X))) have zero K1 class. Choose N such that
diag(u,1_(N-r)) is null-homotopic. Suppose a diagonal map takes M_r(C(X))
to M_R(C(Y)), R >= N, with eigenvalue maps lambda_1,...,lambda_m.
Its image of u is a product of m unitaries, each equal to u composed with
one lambda in its own r-dimensional block and equal to the identity
elsewhere. Each factor is conjugate by a constant permutation to
diag(u composed with lambda,1_(R-r)); pullback of the chosen stabilized
homotopy contracts it. Multiplying these homotopies contracts the product.
The contractions need not preserve the original diagonal subalgebra.
No restriction on dim(Y), or on the number of different eigenvalue maps,
is used. The same argument works for finite direct sums, using a common
stabilization size for the finitely many source components.

This explains exactly why replacing a seed by more coordinate copies
does not, by itself, preserve a K1-trivial unstable unitary.

## 2. A bundle-sensitive contraction criterion

Let E be a Hermitian bundle on X and u a unitary automorphism. Suppose
u direct-sum 1_(E^s) is homotopic to 1 on E^(s+1). Let

    F = direct-sum over l of F_l,
    F_l = lambda_l^*E tensor L_l

on Y, where the L_l are Hermitian multiplicity bundles. Put
v_l = lambda_l^*u tensor 1_(L_l). If, for every l, the complement
F minus F_l contains a subbundle isomorphic to F_l^s, then

    direct-sum_l v_l is null-homotopic in U(End(F)).

Proof: tensor and pull back the stipulated homotopy. Use the assumed
subbundle to place it inside F, acting as the identity on its orthogonal
complement. It contracts the unitary acting by v_l on F_l and by the
identity elsewhere. The product of these finitely many unitary
homotopies contracts their product, which is direct-sum_l v_l.
The spare subbundles can overlap: they are used in separate factors.

A useful variant replaces E^s by any explicitly available stabilizing
bundle T. If u direct-sum 1_T is null and the complementary target
bundle contains lambda^*T tensor L, the corresponding factor contracts.
This variant is what the next calculation uses.

Failure of the subbundle condition is only failure of this sufficient
criterion. It does not prove that the unitary is non-null-homotopic.

## 3. An explicit twisted eigenvalue map

Fix a basepoint x_0 in S^4 and a based map

    u : S^4 -> U(2),   [u] generating pi_4(U(2)) = Z/2.

It is not null-homotopic, but u direct-sum 1 is null in U(3), since
pi_4(U(3)) = 0. For k >= 0 let L be the tautological line bundle on
CP^k and pull all bundles to X_k = S^4 x CP^k. Define

    F_k = C^2 direct-sum (L tensor C^2),
    phi_k(f)(x,z) = f(x) direct-sum (1_(L_z) tensor f(x_0)),
    v_k = phi_k(u) = u direct-sum 1_(L tensor C^2).

This is a unital injective *-homomorphism
M_2(C(S^4)) -> Gamma(End(F_k)). Injectivity follows from the first
block. The second block is an actual point evaluation with multiplicity
bundle L; this is a twisted homogeneous construction, rather than a
globally diagonal map between full matrix bundles.

Every v_k has zero K1 class. Indeed phi_k induces a map on K1, and the
class of u is already zero before applying phi_k. Independently, X_k
has a finite CW decomposition with only even-dimensional cells. Bott
periodicity and the cellular exact sequences give K1(C(X_k)) = 0;
Morita equivalence gives the same for Gamma(End(F_k)).

For k = 0 or 1, v_k is null-homotopic. For k = 0 this is ordinary
stabilization. For k = 1, L direct-sum L has a nowhere-zero section:
identify CP^1 with lines ell in C^2, let P_ell be orthogonal projection,
and take

    s(ell) = (P_ell e_1, P_ell e_2) in ell direct-sum ell.

Its squared norm is trace(P_ell) = 1. Thus L direct-sum L contains a
trivial line. Use the based null-homotopy of diag(u,1) on the C^2
summand plus this line, and use the identity on the orthogonal
complement. This homotopy is the identity above {x_0} x CP^1.

For k = 2 the same spare line is impossible: writing h for either
signed generator of H^2(CP^2;Z),

    c_2(L direct-sum L) = h^2 != 0.

A nowhere-zero section would split off a trivial line, leaving a line
bundle, whose total Chern class has no degree-four term. This proves
that CP^2 is the first projective base in this specific construction
where the displayed contraction criterion fails. It DOES NOT prove
that v_2 survives. Nonzero Euler class is not an invariant of a
unitary homotopy class.

The homotopy groups used here and below follow from Bott's computation
pi_(2n)(U(n)) = Z/(n!) and the stable range from
U(n) -> U(n+1) -> S^(2n+1). See
[Bott, The stable homotopy of the classical groups, p. 315](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/bott4.pdf).

## 4. The first twisted test reduces to a specific finite quotient

Write X = S^4 x CP^2 and

    Z = (S^4 x CP^1) union ({x_0} x CP^2).

Let G_X be the group of continuous unitary automorphisms of F_2,
G_Z the corresponding group over Z, and G_(X,Z) the subgroup of G_X
whose restrictions to Z are the identity. The section restriction map
has the homotopy lifting property onto the components in its image.
One can see this directly: subdivide a unitary path into increments
near 1, take their self-adjoint logarithms, extend those sections from
the closed subcomplex using bundle charts and a partition of unity,
and exponentiate. The same construction with parameters gives the
usual relative lifting property. Consequently there is an exact sequence

    pi_1(G_Z,1) --boundary--> pi_0(G_(X,Z))
                  -> pi_0(G_X) -> pi_0(G_Z).

The product CW structure has exactly one cell outside Z, of dimension
8. Pull F_2 back to its characteristic disk D^8 and trivialize it.
A section equal to 1 on Z is then precisely a map D^8 -> U(4) equal
to 1 on its boundary. Boundary trivializations cause no ambiguity
because conjugating the identity still gives the identity. Therefore

    pi_0(G_(X,Z)) = pi_8(U(4)) = Z/24.

Section 3 constructs a null-homotopy of v_2 on S^4 x CP^1 which is
the identity above x_0. Glue it to the constant path on
{x_0} x CP^2. Lift that path to G_X starting at v_2. Its endpoint
w belongs to G_(X,Z), giving q = [w] in Z/24. If D denotes the image
of the displayed boundary map, exactness gives the precise test

    [v_2] = 0 in pi_0(G_X)  if and only if  q is in D.

The coset q+D is independent of the chosen lifted contraction.
Furthermore 2(q+D) = 0: phi_2 induces a group homomorphism on
components, and the original [u] has order two. Thus only an element
of order at most two in the finite cyclic quotient (Z/24)/D can be
the obstruction. This reduction includes the boundary ambiguity;
declaring a nonzero element of Z/24 without quotienting by D would
be an invalid survival proof.

This is an exact finite-stage reduction, not a computation of q or D.
The subsequent complete manuscript proves that q+D is nonzero of
order two, constructs compatible connecting maps preserving the
class at every later stage, and proves the resulting limit simple.
It does not identify the particular subgroup D inside Z/24.

## 5. Scope of this initial reduction

The boundary map not calculated by this initial reduction is
pi_1(G_Z) -> Z/24 together with the element arising from the displayed
rank-three contraction on CP^1. It must retain the twisting action of
L direct-sum L and the attaching map of the four-cell of CP^2.
Using the abstract group pi_8(U(4)) alone, or a Chern-number heuristic,
does not determine that map. No speculative value is recorded as a
Cairn theorem. The subsequent mapping-torus parity proof resolves
survival without needing to identify this boundary map.

The diagonal literature result is attributed to its authors. The new
work recorded here is the explicit target selection, elementary
contractions, and finite obstruction reduction. They narrow an existing
LIX construction attempt; the complete answer is in the subsequent
manuscript, not in the reduction alone.
