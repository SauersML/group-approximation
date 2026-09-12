# Finitely presented sofic groups with perfect, residually finite MF radical

Date: 2026-09-07.

This artifact contains the finite-dimensional fixed-algebra and
finite-block proofs. It imports the one-sided Kazhdan transport and
trace results retained in `non_mf_groups_exist.tex`, together with the
explicitly identified classical inputs below. The manuscript's former
finite-block sections can be found historically at revision
`5ba20cc934b4cdcf4acf5bfc6ae172111b0dd8e1`; they are not in the current
paper. This artifact does not claim a new Lean kernel check or
literature priority.

The two additions are a fixed-point theorem for **finite-dimensional
invariant C*-subalgebras**, and a construction with **finite blocks** of
finite perfect groups. The latter is finitely presented; the unrestricted
permutational wreath construction is not. Its MF radical is computed exactly
and is itself perfect and residually finite.

## 1. Finite-dimensional lifting and covariance

Write Q = product M_(d_n)(C) / direct-sum M_(d_n)(C), with the direct sum
meaning operator-norm-null sequences.

**Lifting fact.** A unital *-homomorphism phi:A -> Q from a
finite-dimensional C*-algebra has, after discarding finitely many coordinates,
unital *-homomorphic lifts phi_n:A -> M_(d_n)(C). They need not be injective.

Here is the matrix-unit construction. Write A as a finite direct sum of
full matrix algebras. Lift its diagonal matrix units to self-adjoint matrices.
Round them successively to orthogonal projections, performing each new
rounding in the complement of the earlier projections. The rounding errors
tend to zero, because the original relations hold in Q. Use the complement
of their sum for the last diagonal projection; the sum is then exactly one.
For a summand M_r, compress a lift of e_(i1) between the chosen diagonal
projections p_i and p_1. Its two products with its adjoint tend to p_i and
p_1. On a sufficiently late tail both errors are less than one, so the
compressed matrix is invertible between these ranges. Its polar partial
isometry v_i has initial projection p_1 and final projection p_i and differs
from the compressed lift by a norm-null sequence. Set v_1=p_1 and lift e_ij
by v_i v_j*. These are exact matrix units. Different summands are orthogonal.
This gives the claimed unital lifts, including coordinates on which a whole
summand is zero.

**Covariance fact.** Suppose beta is an automorphism of A, U_n are unitaries,
and

    || U_n phi_n(a) U_n* - phi_n(beta(a)) || -> 0   (a in A).

There are unitaries Z_n with ||Z_n-1|| -> 0 for which

    (Z_n U_n) phi_n(a) (Z_n U_n)* = phi_n(beta(a))   (a in A).

To prove this, put f_n=Ad(U_n) phi_n and g_n=phi_n beta. Finite
dimensionality makes their difference converge uniformly on the unit ball.
With normalized Haar measure on the compact group U(A), set

    T_n = integral_(u in U(A)) g_n(u) f_n(u)* du.

Then ||T_n-1|| -> 0, and left invariance gives
T_n f_n(u)=g_n(u) T_n. For large n, T_n is invertible. Its polar unitary
Z_n=T_n(T_n*T_n)^(-1/2) has the same intertwining property: T_n*T_n
commutes with f_n(A). Continuity of polar decomposition at one gives
||Z_n-1|| -> 0. Unitaries linearly span A, so the identity holds on A.

## 2. Finite-dimensional fixed-point transport

**Theorem 1.** Let G be countable, L <= G have property (T), and
t L t^-1 <= L. Let rho:G -> U(Q) be a homomorphism. If A <= Q is a
finite-dimensional unital C*-subalgebra normalized by rho(L), then

    A^(Ad rho(t L t^-1)) = A^(Ad rho(L)).                  (1)

In particular, if F <= G is finite and normalized by L, and f in F
centralizes t L t^-1, then rho(f) centralizes rho(L). Neither normality of
F in G nor commutativity of its conjugation orbit is required.

**Proof.** Lift rho to an operator-norm asymptotic representation U_n of G
and lift A by the homomorphisms phi_n of Section 1. Choose a finite symmetric
generating Kazhdan set S for L and a Kazhdan constant kappa>0. Write
beta_g=Ad(rho(g))|_A. Correct U_n(s), for the finitely many s in S, by the
covariance fact to unitaries V_n(s) implementing beta_s exactly on phi_n(A),
with ||V_n(s)-U_n(s)|| -> 0.

For all large n, ker(phi_n) is invariant under every beta_s, hence under L.
Moreover the trace tr_(d_n) phi_n is invariant under beta_s, hence under L.
Consequently

    pi_n(g) phi_n(a) = phi_n(beta_g(a))

is a well-defined, genuine unitary representation of L on the Hilbert space
A_n=phi_n(A), with normalized Hilbert--Schmidt inner product. This is true
even when phi_n is not faithful. A word for each fixed g in the generating
set S gives a unitary V_n(g) implementing pi_n(g) on A_n. Asymptotic
multiplicativity of U_n gives ||V_n(g)-U_n(g)|| -> 0. Thus the implementing
error on HS vectors is uniform in their matrix dimension and their rank:

    || Ad(U_n(g))x - pi_n(g)x ||_2
        <= 2 ||U_n(g)-V_n(g)|| ||x||_2   (x in A_n).       (2)

Put H=tLt^-1. Suppose a in A is H-fixed but not L-fixed. Let E_n be the
orthogonal projection in A_n onto its pi_n(L)-fixed vectors, and put
b_n=phi_n(a)-E_n phi_n(a). Infinitely many b_n are nonzero: otherwise
phi_n(beta_g(a)-a)=0 eventually for every g, contrary to the choice of a.
Retain those coordinates and put x_n=b_n/||b_n||_2. Then ||x_n||_2=1,
x_n is orthogonal to the pi_n(L)-fixed vectors, and pi_n(h)x_n=x_n for
every h in H. The last assertion holds because both phi_n(a) and
E_n phi_n(a) are H-fixed. By (2),

    || Ad(U_n(h))x_n-x_n ||_2 -> 0   (h in H).             (3)

Now apply the HS-bounded transport theorem `thm:transport`, retained in
the current manuscript. The sequence y_n=Ad(U_n(t))*x_n is asymptotically L-fixed
by (3) and the relation tLt^-1=H. Transporting y_n forward by t makes x_n
asymptotically L-fixed. Equation (2) then implies

    max_(s in S) || pi_n(s)x_n-x_n ||_2 -> 0.

The Kazhdan inequality on the orthogonal complement of the fixed vectors
instead bounds this maximum below by kappa ||x_n||_2=kappa. Contradiction.
This proves the nontrivial containment in (1); the other is H<=L.

For the group statement use A=C*(rho(F)), which is finite dimensional,
unital, and normalized by rho(L). Apply (1) to a=rho(f). QED.

This proof uses the ordinary HS-bounded transport theorem at unit mass.
Exact covariance is established before normalizing b_n. Thus no error is
divided by an uncontrolled rank or HS mass. It uses neither the affine
fixed-point theorem nor a rescaled displacement cocycle.

## 3. The finite-block construction

Let Gamma be a finitely presented property-(T) group and let
alpha:Gamma -> Gamma be injective with finite index m>1. Assume that its
ascending HNN extension

    V = <Gamma,t | t gamma t^-1=alpha(gamma)>

is residually finite. In particular Gamma is residually finite. Set

    Gamma+ = t^-1 Gamma t,
    X = V/Gamma,     Y = V/Gamma+,
    p:X -> Y,       p(v Gamma)=v Gamma+.

Every fiber of p has m points. For a finite group K let K_x be a labeled
copy of K at x in X, and define

    B_K = *_(y in Y) (product_(x in p^-1(y)) K_x),
    G_K = B_K semidirect V.                              (4)

The free product is the ordinary free product, with trivial edge groups.
The action of V permutes the labeled coordinates. In particular every K_x
and every block K^m embeds, by free-product normal form. This is the point
at which nontriviality of the lamp subgroup is established.

**Theorem 2.** The group G_K is finitely presented and is J_K semidirect Z
with J_K locally residually finite. Every homomorphism from G_K to an MF
group factors through the canonical quotient

    q_K:G_K -> ( *_(y in Y) K_ab ) semidirect V
               ~= V *_(Gamma+) (Gamma+ x K_ab).           (5)

The target of (5) is MF, and therefore

    Rad_MF(G_K) = ker(q_K).                              (6)

If K is nontrivial and perfect, then

    Rad_MF(G_K) = Res_fin(G_K) = B_K,
    G_K/Rad_MF(G_K) ~= V.                                (7)

Here B_K is nontrivial, perfect, and residually finite. The group G_K is
sofic but not MF. The canonical trace of C*_max(G_K) is amenable and not
quasidiagonal. If K is nonabelian simple, every nonidentity element of
one coordinate K_x normally generates B_K in G_K.

### Finite presentation

Choose finite presentations Gamma=<S|R> and K=<Z|T>. Choose right-Gamma
coset representatives b_1=1,b_2,...,b_m in Gamma+. Express them as words
in S and t. A finite presentation of G_K has generators S,t,Z and relators

    R, T;
    t s t^-1 = alpha(s)                    (s in S);
    [z,s] = 1                             (z in Z, s in S);
    [z,b_i z' b_i^-1] = 1                 (z,z' in Z, 2<=i<=m).  (8)

To verify equality, first omit the last family. Adjoining K centralized by
Gamma to V gives V *_Gamma (Gamma x K). Its kernel under the retraction
to V is the free product of the K_x, x in X: this follows either from the
amalgam normal form or directly by constructing the two homomorphisms
between the displayed presentation and (*_X K_x) semidirect V.
The last family imposes commutation of the root coordinate with every other
coordinate of its p-fiber. Conjugating by V imposes exactly commutation
between all distinct coordinates in each fiber. Indeed any pair in a
fiber is vGamma,vb_iGamma for some v in V and i>1. Different fibers acquire
no relations. The resulting presentation is exactly (4), proving (8).

### Collapse and exact MF quotient

The block over tGamma+ is the set {gamma tGamma:gamma in Gamma}. It is
Gamma-invariant and has m points. Its finite group F=K^m is normalized by
Gamma. A root element k_(tGamma) is centralized by
tGamma t^-1=alpha(Gamma). Apply Theorem 1 with L=Gamma to see that

    rho(k_(gamma tGamma))=rho(k_(tGamma))   (gamma in Gamma, k in K).

Translation by V gives equality of the copies of any k throughout each
fiber. Two distinct coordinates in a fiber commute, so, after this
identification, the common image of K is abelian. This proves that every
corona homomorphism factors through (5), and the same holds for MF targets
by composing with an MF embedding. The kernel of (5) is normally generated
by the within-fiber identifications and the coordinate commutators. Its
quotient is the displayed free product of the block abelianizations,
semidirect V. The last isomorphism in (5) follows from the same free-product
kernel calculation used for (8).

For general K the MF upper bound uses one external theorem: Shulman,
arXiv:2603.13564v2, Theorem 10. Here are the group-embedding details, to
avoid silently strengthening its C*-algebraic statement. Put D=V x K_ab,
which is residually finite, and embed D into a norm matrix corona using
regular representations of finite quotients separating an exhaustion.
Let A be the C*-algebra generated by that image and C the algebra generated
by Gamma+ x {1}. Along any free ultrafilter, normalized matrix traces give
a trace tau on A with tau(rho(d))=0 for d!=1. Its GNS representation on D
is the regular representation, and hence its von Neumann completion is
L(D), with the completion of C equal to L(Gamma+).

Shulman's theorem makes A *_C A MF. The two GNS maps induce a
*-homomorphism from this full C*-amalgam to the tracial von Neumann amalgam
L(D) *_(L(Gamma+)) L(D). A reduced group word from D *_(Gamma+) D
has trace zero there by the defining conditional expectations, so cannot
equal one. Thus D *_(Gamma+) D embeds in U(A *_C A) and is MF.
The group in (5) embeds in this double by putting V in the first copy
and Gamma+ x K_ab in the second; a reduced word remains reduced. This
proves that the target of (5) is MF and gives (6).

For perfect K the target is just V, so Shulman's theorem is unnecessary
for (7). All maps to MF groups kill B_K, and the residually finite quotient
V separates every element outside B_K. Since finite groups are MF, the
same two containments prove Res_fin(G_K)=B_K.

### Residual finiteness of B_K and its local extensions

A finite free product of finite groups is residually finite: its map to
their direct product is injective on each free factor. The kernel therefore
acts freely on the free-product tree and is free. It has finite index,
is finitely generated, and is residually finite; taking the finite
intersection of conjugates of a finite-index normal subgroup in this
kernel proves residual finiteness of the whole group. Alternatively this
is the elementary virtually free case of the tree normal-form theorem.
Every nontrivial element of B_K lies in a finite sub-free-product, and the
retraction onto that sub-free-product preserves it. Thus B_K is residually
finite. When K is perfect, each factor K^m is perfect, and the abelianization
of their free product is trivial, so B_K is perfect.

Let T_alpha=union_(n>=0) Gamma_n, with Gamma_n=t^-n Gamma t^n. The HNN
height map identifies V=T_alpha semidirect Z and G_K=J_K semidirect Z,
where J_K=B_K semidirect T_alpha. Finite index of alpha(Gamma) makes
Gamma commensurated by V, so each Gamma_n has finite orbits on X and Y.
Explicitly Gamma_n is commensurate with every vGamma v^-1, and its orbit
at vGamma has size [Gamma_n:Gamma_n intersect vGamma v^-1].

A finite subset of J_K involves finitely many blocks and actor coordinates
in some Gamma_n. Saturate those blocks under Gamma_n; this gives a finite
invariant set I. The subgroup in question lies in

    M_I semidirect Gamma_n,       M_I = *_(y in I) K^m.

The action factors through permutations of the m|I| labeled sites. Its
kernel Lambda has finite index in Gamma_n and centralizes M_I. Therefore
M_I x Lambda is residually finite and has finite index in the displayed
semidirect product, which is consequently residually finite. This proves
that J_K is locally residually finite.

Local residual finiteness and the amenable quotient Z make G_K sofic
(Elek--Szabo, Theorem 1). The current manuscript's retained
`prop:locally-rf-by-z-trace` proves amenability of the canonical maximal
trace, and `thm:factorization-nonmf-trace` proves its failure of
quasidiagonality whenever K is nontrivial perfect.

For nonabelian simple K, the normal closure of a nonidentity k in K_x
contains K_x by simplicity, then all K_(vx) by transitivity of V on X,
and therefore B_K. The reverse containment holds because B_K is normal.

## 4. An explicit centerless specialization

Take

    Gamma = Z^3 semidirect SL_3(Z),
    alpha(v,A)=(2v,A),        K=A_5.

Use the property-(T) assertion (BHV, Example 1.7.4(i)), also retained
in the current manuscript, and the following faithful affine model:

    V = { [[2^h A, v],[0,1]] : h in Z, A in SL_3(Z),
                                v in Z[1/2]^3 }.

Reduction modulo odd integers separates V. The base Gamma is finitely
presented: the repository's explicit twenty-relator presentation is
identified with this affine group by
`LiteralBaseCompleteness.baseAffineEquiv`; alternatively use the classical
finite presentation of SL_3(Z) and the finite semidirect-product relations.
Here m=8 and Y is countably infinite, since the height map descends from
V to V/Gamma+. Hence the theorem gives

    1 -> *_(j in N) (A_5)^8 -> G_(A_5) -> V -> 1,        (9)

a split exact sequence of residually finite kernel and quotient, with

    Rad_MF(G_(A_5)) = Res_fin(G_(A_5))
                   = *_(j in N) (A_5)^8 != 1.           (10)

The group G_(A_5) is finitely presented, sofic, and not MF. Its MF radical
is perfect, residually finite, and normally generated by any nonidentity
element of one A_5 coordinate. Thus it is an MF group as an abstract group
even though every ambient MF representation kills it.

It is centerless. An element of Z(V) commuting with all translations must
have 2^h A=I; determinants force h=0 and A=I. Its translation vector must
then be fixed by every integral elementary matrix, so is zero. Thus
Z(V)=1. A central element of G_(A_5) lies in B_(A_5), whose center is
trivial because it is a free product of at least two nontrivial groups.

## 5. What this adds, and the proof boundary

The fixed-algebra theorem and perfect-lamp construction are proved in
Sections 1--4 above. They were also printed in `non_mf_groups_exist.tex`
at historical revision `5ba20cc934b4cdcf4acf5bfc6ae172111b0dd8e1`, under
`thm:finite-algebra-transport`, `thm:perfect-block-radical`, and
`thm:fp-sofic-radical`; those statements were subsequently removed
from the paper. The arbitrary finite-lamp quotient (5)--(6) is proved
in this artifact.

* The finite-dimensional fixed-point theorem extends
  `finite-noncommutative-packet-compression-collapse` to an invariant
  finite-dimensional C*-algebra and gives it a proof without the older
  weighted cocycle or affine fixed-point argument.
* The group construction differs from the established unrestricted wreath
  theorem: only coordinates in a finite p-fiber commute. It retains finite
  presentability, which the unrestricted compression wreaths lack.
* It differs from the older literal Clifford construction: for perfect K the
  entire free-product lamp kernel is the MF radical, the quotient is the
  explicit residually finite affine V, and the example is centerless.
* The proof uses the current manuscript's retained `thm:transport` and
  trace propositions,
  finite-dimensional C*-algebra lifting as proved above, property (T) of the
  affine base, elementary free-product/tree theory, and sofic closure under
  locally residually finite-by-Z extensions. Only the optional arbitrary-K
  quotient in (5)--(6) uses Shulman's C*-amalgam theorem:
  <https://arxiv.org/html/2603.13564v2#S3.Thmtheorem10>.
* Cairn checks the dependency graph. It does not kernel-check this proof.
  The new theorems do not yet have compiled Lean declarations.
