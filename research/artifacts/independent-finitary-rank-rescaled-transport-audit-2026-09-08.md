# Independent audit: finitary rank bounds and rescaled Kazhdan transport

2026-09-08. This is an independent handwritten audit of the proposed
norm-corona argument. It supplies the finite-lifting and weighted-error
details. It is not a proof-assistant certificate. No code or build was
executed locally in this audit.

The argument checks under the stated uniform finite-group rank bound.
It does not prove the unrestricted assertion for every locally finite
normal subgroup. For the normal finitary elementary group over Z/q,
the necessary rank bound has the elementary proof below.

## 1. A finite-group rank bound, including composite q

Fix q>=2 and m>=3, and write R=Z/q. Let

    F=EL_m(R)=SL_m(R),      a=I+E_12 in F.

The equality follows, for example, by elementary elimination over the
finite product of local rings given by the Chinese remainder theorem.
Let sigma:F->U(H) be any finite-dimensional complex representation.
Write p_F for the projection onto H minus Fix(sigma(F)), and p_a for
the projection onto H minus Fix(sigma(a)). Then

    rank(p_F)<=4 rank(p_a).                            (1)

There is no irreducibility assumption and the constant is independent
of q, m, and dim(H).

Put r=m-1, and take the row and column groups

    U={I+sum_(j=2)^m x_j E_1j : x_j in R},
    V={I+sum_(i=2)^m y_i E_i1 : y_i in R}.

They are abelian, each isomorphic to R^r. The embedded Levi group
SL_r(R) normalizes U and is transitive on the characters of each
effective modulus k>1 dividing q. More explicitly, such characters
are parametrized by primitive vectors b in (Z/k)^r, where
gcd(b_1,...,b_r,k)=1. The character indexed by b takes value one on
a exactly when b_1=0 mod k. Surjectivity of SL_r(R)->SL_r(Z/k) and
elementary completion of primitive vectors give the transitivity.

Within one such orbit the character multiplicities in sigma|_U are
constant, because the Levi acts unitarily. The fraction of vectors
having b_1=0 is

    [k^(r-1) product_(p|k)(1-p^(-(r-1)))]
      /[k^r product_(p|k)(1-p^(-r))]
      <=1/k<=1/2.                                    (2)

This counts primitive vectors by the Chinese remainder theorem.
Consequently at least half of the nontrivial U-character mass is
moved by a, and

    codim Fix(sigma(U))<=2 rank(p_a).                  (3)

Apply the same calculation to V. Its distinguished transvection
I+E_21 is conjugate in F to a or a^(-1) by a determinant-one signed
permutation; either choice has the same fixed-space dimension. Thus

    codim Fix(sigma(V))<=2 rank(p_a).                  (4)

The groups U and V generate EL_m(R): they contain every elementary
root with row or column 1, and

    [I+x E_i1,I+E_1j]=I+x E_ij       (i,j>1, i!=j)

gives the remaining roots. Hence their invariant-space intersection
is Fix(sigma(F)). Codimension subadditivity applied to (3)--(4)
proves (1).

For q=2 one can count directly: all nonzero U-characters have one
common multiplicity and exactly 2^(r-1) of the 2^r-1 characters are
nontrivial on a. This gives the slightly stronger coefficient
4-2^(2-r) in (1), but only the uniform constant 4 is needed.

## 2. Abstract finite-stage hypotheses

Let G be countable and contain a normal subgroup

    A=union_m F_m,

where F_m is an increasing sequence of finite groups. Fix a finite
order element a in F_1. Suppose there is K<infinity such that every
finite-dimensional representation sigma of every F_m obeys

    rank(1-P_Fm)<=K rank(1-P_a),                       (5)

where the P's are invariant-vector projections.

For A=EL_fin(Z/q), take standard finite coordinate groups
F_m=EL_m(Z/q), all containing the same root a=I+E_12. Section 1 gives
K=4. If another enumeration of the countable basis is used, start the
exhaustion after it contains the two indices of a.

Let rho:G->U(Q_d) be a norm-matrix-corona homomorphism. Choose exact
unitary lifts V_n(g) for the group elements, so V_n is an
operator-norm asymptotic representation. Suppose rho(a)!=1. Since a
has finite order, on an infinite coordinate subsequence a sufficiently
close exact finite-order lift of rho(a) is nontrivial. All later
coordinate choices are taken in this subsequence.

We construct positive contractions e_j and positive integers r_j
such that, with

    ||x||_(2,r_j)=(Tr(x*x)/r_j)^(1/2),

the following hold:

    ||e_j||_(2,r_j)<=sqrt(K),                           (6)
    ||[e_j,V_j(g)]||_(2,r_j)->0       for every g in G,  (7)
    liminf ||(V_j(a)-1)e_j||_(2,r_j)>=eta_a>0.           (8)

Here eta_a is the minimum distance from 1 of a nontrivial root of
unity of order dividing the fixed order of a.

## 3. One finite lift per coordinate gives coherent projections

Choose finite symmetric sets K_j increasing to G. For each j choose
a chain of standard finite stages

    F_(j,0)<=F_(j,1)<=...<=F_(j,j+1)

all containing a, such that

    g F_(j,i) g^(-1)<=F_(j,i+1)
      for g in K_j and 0<=i<=j.                       (9)

Normality of A supplies this chain: each conjugate of one finite
stage is a finite subset of A and therefore lies in a later stage.
The symmetry of K_j also gives

    F_(j,i-1)<=g F_(j,i) g^(-1)<=F_(j,i+1)
      for 1<=i<=j.                                   (10)

The homomorphism rho|_(F_(j,j+1)) is a unital representation of the
finite-dimensional C*-algebra C*(F_(j,j+1)) in the norm corona.
Finite-dimensional C*-algebra maps to a norm matrix corona lift on
a coordinate tail to unital *-homomorphisms into the same matrix
coordinates. This is the ordinary matrix-unit lifting argument:
round diagonal projections, polar-correct the off-diagonal matrix
units between them, and use the complement for the final projection.
Zero summands are permitted; no faithfulness of coordinate lifts is
required. Thus there are exact finite-group representations

    sigma_n^(j):F_(j,j+1)->U(d_n)

which differ from V_n on each element of this fixed finite group by
an operator-norm-null sequence.

For this fixed j, covariance and asymptotic multiplicativity imply

    ||V_n(g)sigma_n^(j)(b)V_n(g)*
         -sigma_n^(j)(g b g^(-1))||_op ->0              (11)

uniformly over the finite collection g in K_j, b in F_(j,i),
0<=i<=j. Choose one coordinate n_j sufficiently far out that all
these errors and ||V_(n_j)(a)-sigma_(n_j)^(j)(a)||_op are at most
delta_j, where delta_j->0, and that the exact a lift is nontrivial.
Choose n_j strictly increasing. This is diagonal selection from
already existing coordinate tails, not a rate assertion about r_j/d_j.

At coordinate j use this ONE representation sigma_j of the largest
finite group to define every projection in the chain:

    p_(j,i)=1-|F_(j,i)|^(-1)
                   sum_(b in F_(j,i)) sigma_j(b),
    p_(a,j)=1-|<a>|^(-1)sum_(b in <a>)sigma_j(b),
    r_j=rank(p_(a,j))>0.

These are exact orthogonal projections, and

    p_(a,j)<=p_(j,0)<=...<=p_(j,j+1),
    rank(p_(j,i))<=K r_j.                             (12)

The first statement follows from the inclusion of fixed spaces and
the second is (5). Using unrelated lifts for the different chain
stages would not justify (12); the common largest-stage lift is
essential.

For g in K_j, let p'_(j,i,g) be the active projection of the subgroup
g F_(j,i) g^(-1), computed in the same sigma_j. Then (10)--(11) give

    p_(j,i-1)<=p'_(j,i,g)<=p_(j,i+1),
    ||V_j(g)p_(j,i)V_j(g)*-p'_(j,i,g)||_op<=delta_j,    (13)

where V_j=V_(n_j). Set

    e_j=j^(-1)sum_(i=1)^j p_(j,i).                    (14)

It is a positive contraction, is supported on p_(j,j), and
e_j p_(a,j)=p_(a,j). Summing the order bounds in (13), the lower and
upper index shifts telescope:

    e_j-(1/j+delta_j)1
      <=V_j(g)e_j V_j(g)*
      <=e_j+(1/j+delta_j)1.                           (15)

Therefore

    ||[e_j,V_j(g)]||_op<=1/j+delta_j.                 (16)

The commutator has rank at most 2 rank(e_j)<=2K r_j, regardless of
the covariance errors. Consequently

    ||[e_j,V_j(g)]||_(2,r_j)
      <=sqrt(2K)(1/j+delta_j)->0.                     (17)

This proves (6)--(7); each fixed g belongs to all sufficiently large
K_j. Crucially, no estimate multiplies an operator-norm error by
sqrt(d_j/r_j). The rank in (17) is the actual rank of the actual
commutator.

Finally sigma_j(a)-1 is supported on p_(a,j), on which e_j acts as
the identity. Its nonzero eigenvalues have modulus at least eta_a.
Thus

    ||(sigma_j(a)-1)e_j||_(2,r_j)>=eta_a.

Replacing sigma_j(a) by V_j(a) costs at most
sqrt(K)||sigma_j(a)-V_j(a)||_op, proving (8). In the binary case a
is an involution and the displayed norm is exactly 2 before this
replacement.

## 4. Rescaled transport is a direct consequence of the manuscript

The one-sided Kazhdan transport theorem in non_mf_groups_exist.tex
applies to Hilbert--Schmidt bounded sequences; it places no operator
norm bound on those sequences. It therefore applies verbatim to
||.||_(2,r_j) for any positive scalars r_j.

Indeed, if x_j is bounded in the latter norm, set

    y_j=sqrt(d_j/r_j) x_j.

Then ||y_j||_(2,d_j)=||x_j||_(2,r_j), and multiplication by the
scalar sqrt(d_j/r_j) commutes with every coordinate adjoint action.
The original theorem applied to y_j is exactly the rescaled theorem
for x_j. Equivalently, scalar rescaling of the Hilbert inner product
does not change the operator norms of the adjoint operators or the
finite-dimensional operator corona used for Kazhdan projection.

This deduction uses neither a displacement cocycle nor a new
Delorme--Guichardet argument.

## 5. Quasicentral bounded carriers make the defect vanish

Let L<=G have property (T), and let uLu^(-1)<=L. Let c centralize L
and put d=ucu^(-1). Use the carriers from Section 3. The sequence

    x_j=V_j(c)e_j

is bounded in ||.||_(2,r_j), by (6), and is asymptotically L-central.
For ell in L this follows from

    [V_j(ell),V_j(c)e_j]
      =[V_j(ell),V_j(c)]e_j+V_j(c)[V_j(ell),e_j].       (18)

The first term tends to zero in the rescaled norm because its first
factor tends to zero in operator norm and e_j has bounded rescaled
norm. The second tends to zero by (7).

Rescaled one-sided transport makes

    V_j(u)V_j(c)e_j V_j(u)*

asymptotically L-central. By (7) and asymptotic multiplicativity it
differs in the rescaled norm by o(1) from V_j(d)e_j. Expanding the
commutator of this last sequence with V_j(ell) and using (7) gives

    ||[V_j(d),V_j(ell)]e_j||_(2,r_j)->0.              (19)

Move e_j through the fixed product V_j(d)*V_j(ell)* using (7), and
use operator-norm asymptotic multiplicativity with e_j on the right.
Equation (19) implies

    ||(V_j([d,ell])-1)e_j||_(2,r_j)->0.               (20)

All replacements of group words by products are multiplied by e_j
or a unitarily conjugate copy of it. The errors are bounded by a
fixed multiple of sqrt(K) times the operator-norm defect. The raw
identity matrix need not be bounded in the rescaled Hilbert norm.

For completeness define

    N_e={g in G:||(V_j(g)-1)e_j||_(2,r_j)->0}.

It is a normal subgroup. Product and inverse closure follow from
asymptotic multiplicativity and the triangle inequality, with error
terms bounded using (6). For conjugation by a fixed k, the difference
between V_j(k g k^(-1)) and V_j(k)V_j(g)V_j(k)* is operator-norm null,
and

    V_j(k)(V_j(g)-1)V_j(k)*e_j
      =V_j(k)(V_j(g)-1)e_j V_j(k)*
        +V_j(k)(V_j(g)-1)[V_j(k)*,e_j].               (21)

The first summand has rescaled norm
||(V_j(g)-1)e_j||_(2,r_j); the second is at most
2||[V_j(k)*,e_j]||_(2,r_j), which vanishes by (7). Thus N_e is normal.
Since (20) holds for every compression-defect generator, it follows
that

    D_G(L)<=N_e.                                     (22)

If the chosen finite-order mark a belongs to D_G(L), (22) contradicts
(8). Therefore every norm-corona representation kills a. If a
normally generates A, it kills A as well. This is the precise
specialized collapse theorem justified by the argument.

## 6. The universal torsion-defect ring

For q>=2 put

    R_q=Z<s,t | ts=1, q(1-st)=0>,       Q=1-st.

The ideal I=R_q Q R_q is M_fin(Z/q). One direct proof starts with
R_0=Z<s,t|ts=1>. The normal forms s^i t^j form a Z-basis, and

    f_ij=s^i(1-st)t^j

are linearly independent matrix units:
f_ij f_kl=delta_jk f_il. Their span is precisely the ideal I_0
generated by 1-st. The relation q(1-st)=0 quotients R_0 by q I_0,
so I=I_0/q I_0=M_fin(Z/q). The quotient R_q/I is Z[z,z^(-1)].

For G=EL_n(R_q), n>=4, regard M_n(I) as finitary matrices on the
countable index set N times {1,...,n}. The subgroup

    A=EL_fin(Z/q)=SL_fin(Z/q)

is contained in G. Elementary matrices between different exterior
coordinates are x_ab(r f_ij). Elementary matrices between two
distinct internal positions in the same exterior coordinate are
commutators through a different exterior coordinate. Thus every
finitary elementary matrix belongs to G. The natural action by
unilateral shift and backward shift on (Z/q)^(N times {1,...,n}) is
faithful on M_n(I), so this inclusion is injective.

The subgroup A is normal in G. A precise check avoids a determinant
assertion about arbitrary infinite matrices. Every g in G and its
inverse have finite rows and columns in the natural action. The
conjugate of a finitary elementary matrix I+r E_ab is

    I+r v w^T,      v=g e_a,     w^T=e_b^T g^(-1).

Both v and w have finite support, and w^T v=0 because a!=b. On a
finite set containing their supports, the matrix determinant lemma
gives det(I+r v w^T)=1. Thus this conjugate is a finitary determinant-
one matrix, hence lies in EL_fin(Z/q). Applying the same argument to
g^(-1) proves equality under conjugation. Faithfulness on the ideal
identifies this calculation with the conjugation inside G.

The root a=x_13(Q) is the fixed elementary transvection of A. It
normally generates A: its powers supply all coefficients in Z/q,
and finite elementary conjugations move its two indices. The ring
R_q is finitely generated, so the established property-(T) theorem
for elementary groups over finitely generated rings applies to
L=EL_3(R_q). The manuscript's explicit rank-four compression cell
places x_13(Q) in D_G(L). Sections 1--5 therefore kill this root in
every norm-corona homomorphism of EL_n(R_q), n>=4.

If R is ANY unital ring with elements s,t satisfying

    ts=1,       q(1-st)=0,

the universal ring map R_q->R induces an elementary-group map.
Precomposing any MF-target homomorphism of EL_n(R), n>=4, with it
therefore kills x_13(1-st). Conjugation by elementary signed
permutations gives the analogous root in every off-diagonal
position. No finite-generation hypothesis on R and no fullness
hypothesis R(1-st)R=R is needed for this deduction: finite generation
is used only for the universal ring R_q supplying the property-(T)
subgroup. For q=1 the defect is already zero and the conclusion is
immediate.

## 7. Audit boundaries

The proof must retain all of the following:

* one exact largest-stage finite representation for each coordinate;
* nested projections and the two-sided conjugate-stage containment;
* the uniform rank comparison (5), which is additional structure
  beyond local finiteness;
* weighted centrality of e_j for every fixed ambient group element;
* bounded rescaled norm of e_j whenever an operator-norm error is
  converted to a Hilbert--Schmidt error;
* the rescaled transport theorem for arbitrary Hilbert--Schmidt
  bounded sequences, without imposing an operator-bound hypothesis;
* the normality calculation (21), or a direct expression of the mark
  as one compression defect;
* SL_fin rather than GL_fin for composite q, together with the
  determinant-one normality argument in Section 6.

Subject to these explicit details, the rescaling does not leave an
uncontrolled dimension factor. The proposed specialized argument is
a complete mathematical route; formal verification and the final
integration with the manuscript's exact compression cell remain the
parent lane's checks.
