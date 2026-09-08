# Uniform carrier containment for an exact Kazhdan representation

2026-09-08. Handwritten mathematical proof. No local code execution,
build, simulation, or proof-assistant certification is used here.

This closes the coprime-level exact-representation sector of the
arithmetic relative-embedding question. It does not construct a
nonhyperlinear group: arbitrary lattice approximate representations
remain outside the hypotheses, and the small-prime primary exact
sectors require their own analysis.

## 1. The uniform estimate

Let C be a discrete group with a finite Kazhdan pair (S,kappa). Use
the quantitative convention

    ||xi-P_alpha xi|| <= kappa^(-1)
      max_(s in S)||alpha(s)xi-xi||                       (1)

for every unitary representation alpha on a Hilbert space; P_alpha
denotes orthogonal projection onto its invariant vectors. A positive
kappa with this convention exists for every finitely generated
property-(T) group.

Let (M,tau) be finite tracial, let B<=M be a unital von Neumann
subalgebra, and let rho:C->U(M) be an exact group homomorphism. All
distances in M use ||x||_2=tau(x*x)^(1/2). We prove

    sup_(c in C)||rho(c)-E_B(rho(c))||_2
      <= (2/kappa)max_(s in S)||rho(s)-E_B(rho(s))||_2.   (2)

The Jones projection e=e_B from L^2(M,tau) onto L^2(B,tau) belongs to
the basic construction N=<M,e_B>. Its canonical faithful normal
semifinite trace satisfies

    Tr(x e y)=tau(xy),     e x e=E_B(x)e,     Tr(e)=1.    (3)

We do not normalize Tr by Tr(1). The latter may depend on the
inclusion or be infinite; it never appears in the argument.

The formula

    alpha(c)(X)=rho(c) X rho(c)*

defines a unitary representation on L^2(N,Tr). It is a representation
because rho is an exact homomorphism, and is unitary because Tr is
tracial. In particular e is a unit vector in this Hilbert space.

For any u in U(M), set f=u e u*. Both e and f are Tr-finite
projections of trace one. Using (3),

    Tr(e f)=Tr(e u e u*)
           =Tr(E_B(u)e u*)
           =tau(E_B(u)u*)
           =||E_B(u)||_2^2.

The last quantity is real and nonnegative. Hence

    ||u e u*-e||_(2,Tr)^2
      =Tr(f)+Tr(e)-2 Re Tr(e f)
      =2(1-||E_B(u)||_2^2)
      =2||u-E_B(u)||_2^2.                              (4)

Let P=P_alpha and write z=e-Pe. Because Pe is invariant, for every
c in C,

    ||alpha(c)e-e||=||alpha(c)z-z||<=2||z||
      <= (2/kappa)max_(s in S)||alpha(s)e-e||.           (5)

Substitute (4) in (5) and cancel sqrt(2). This proves (2).

No finite dimensionality, finite index, factoriality, hyperfiniteness,
Connes embeddability, or normality of B is needed. The representation
rho must be genuine. The conclusion controls individual group
unitaries uniformly; it does not silently replace that set by the
entire unit ball of the generated algebra.

## 2. Varying words and an approximate slot

Apply (2) independently to exact rho_n:C->U(M_n) and subalgebras
B_n<=M_n. Put

    epsilon_n=max_(s in S)dist_2(rho_n(s),B_n).

For every sequence c_n in C, however long its words are,

    dist_2(rho_n(c_n),B_n)<=2 epsilon_n/kappa.           (6)

If V_n are unitaries with

    eta_n=||V_n-rho_n(c_n)||_2,

then

    dist_2(V_n,B_n)<=eta_n+2 epsilon_n/kappa,            (7)
    ||E_(B_n)(V_n)||_2^2
      >=1-(eta_n+2 epsilon_n/kappa)^2.                  (8)

The right side of (8) may be negative for poor data, in which case
the inequality remains true. In the application eta_n and epsilon_n
both tend to zero, so the expectation norm tends to one.

For matrix coordinates there is also an elementary commutant check
on the mechanism. Every v in U(B_n') obeys

    ||[v,rho_n(s)]||_2<=2 dist_2(rho_n(s),B_n).

Kazhdan projection in L^2(M_n) places v within
2 epsilon_n/kappa of rho_n(C)'. Consequently
||[v,rho_n(c)]||_2<=4 epsilon_n/kappa for every c. Haar averaging over
U(B_n') recovers E_(B_n), giving a weaker constant in (6). This second
calculation confirms that the word-length loss has no mathematical
necessity on the exact representation face.

## 3. The coprime arithmetic application

Let p be prime,

    Lambda=SL_3(Z),    A=SL_3(Z[1/p]),
    h=diag(p,1,p^(-1)).

Suppose U_n:A->U(M_n) are asymptotically multiplicative maps whose
Lambda restrictions sigma_n are genuine representations factoring
through Q_n=SL_3(Z/q_n), with gcd(q_n,p)=1. Suppose subalgebras
B_n<=M_n satisfy the scalar relative-model conditions

    dist_2(sigma_n(s),B_n)->0       for every s in Lambda,
    ||E_(B_n)(U_n(a))||_2->0      for every a outside Lambda.     (9)

The usual model also has canonical trace on A; no trace condition on
the actor is needed for the contradiction below.

The coprime exact-slot theorem gives elements c_n in Lambda, reducing
to h in Q_n, with

    ||U_n(h)-sigma_n(c_n)||_2->0.                       (10)

For completeness, here is the part of that theorem needed here.
Write V'_n=sigma_n(h mod q_n) and V=[U_n(h)] in the tracial
ultraproduct. The subgroup

    Lambda_-=Lambda intersection h^(-1)Lambda h

is finite index in Lambda and contains Lambda(p^2). By the Chinese
remainder theorem, Lambda(p^2) surjects onto Q_n because q_n is
coprime to p; thus sigma_n(Lambda_-)=sigma_n(Lambda).
Both Lambda and Lambda_- have property (T). Their adjoint Kazhdan
estimates show that their relative commutants in the ultraproduct
are the common coordinate commutant

    R_omega=prod_omega(sigma_n(Lambda)' intersection M_n).

Both V and V'=[V'_n] implement conjugation by h on Lambda_-, so
W=V'*V belongs to R_omega. In particular W commutes with all constant
integral matrices and with all congruence slots V'_n, including ones
whose integral representatives vary with n.

Let w_12,w_23 in Lambda be determinant-one signed permutation
matrices for the indicated coordinate transpositions, and set

    h'=w_12 h w_12^(-1)=diag(1,p,p^(-1)),
    h''=w_23 h w_23^(-1)=diag(p,p^(-1),1).

The exact diagonal identity is h(h'')^(-1)=h'. Substituting
V=V'W, and using the preceding commutations, its ultraproduct image
has left side V'_h(V'_(h''))^(-1)=V'_(h') and right side V'_(h')W.
Therefore W=1, proving (10). This is precisely (OSP4) in
odd-congruence-lambda-exact-sector-collapse-proof.

Since Lambda has a fixed finite Kazhdan pair, (7) now gives

    dist_2(U_n(h),B_n)<=||U_n(h)-sigma_n(c_n)||_2
                       +2 epsilon_n/kappa -> 0,        (11)

where epsilon_n=max_(s in S)dist_2(sigma_n(s),B_n). Thus the second
condition in (9) fails at h, which is outside Lambda.

The proof applies to matrix coordinates, as in the existing Cairn
target. It also applies to arbitrary finite tracial coordinates M_n
when the prescribed Lambda representations have the indicated
genuine finite congruence images: adjoint projection, (3)--(5), and
the ultraproduct slot calculation have the same scope. In particular
allowing QWEP coordinates and hyperfinite B_n does not save a model
with these exact congruence hypotheses. We do not claim that an
arbitrary scalar Gao witness admits such exact representatives.

## 4. Why the old counterexample remains valid

The canonical congruence model can have

    [sigma_n(c_n)] outside W*([sigma_n(c)] : c fixed in Lambda).

Nothing above changes this fact. The target carrier prod_omega B_n
has the extra coordinate-subalgebra structure needed for (2).
Pointwise generator containment together with an exact Kazhdan
representation therefore makes the varying slot belong to that
carrier, without making it belong to the constant-sequence subgroup
algebra.

The invalidated route sl3-re-coprime-face-unfaithful-proof remains
invalid. A new route proves its intended target by (11). The
logarithmic-rate estimate remains a valid weaker theorem, but its
previously suggested slow-rate residual sector cannot occur.

## 5. Sources, checks, and remaining gap

The basic-construction identities and canonical trace convention are
the standard ones in Anantharaman--Popa, *An introduction to II1
factors*, Section 9.4, available in the
[authors' text](https://www.math.ucla.edu/~popa/Books/IIun.pdf).
The distance-to-invariants estimate (1) is recorded as Proposition
1.1 in Doucha--Malicki--Valette, *Property (T), finite-dimensional
representations, and generic representations*, citing
Bekka--de la Harpe--Valette Proposition 1.1.9; see the
[published article](https://www.degruyterbrill.com/document/doi/10.1515/jgth-2018-0030/html).
These sources were checked on 2026-09-08. The proof of (2) is supplied
above; no novelty claim is made for this use of the standard tools.

Repository inspection covered the coprime RE claims, their invalidated
proof, the congruence-slot counterexample, the logarithmic-rate route,
the exact-sector Weyl proof, and basic-construction/containment
references. The new estimate establishes the existing open coprime
matrix-form target. It does not establish scalar non-relative-
embeddability for the actual arithmetic pair over all models.

The remaining difficulty is an exact group action in the coordinate
basic-construction Hilbert spaces. An arbitrary approximate actor
does not supply it. Applying property (T) only after taking the
ultraproduct gives an invariant Jones vector for the embedded
constant Lambda algebra; that alone gives no uniform control of
coordinate-varying lattice elements. This is the precise boundary
that the exact representation hypothesis crosses.
