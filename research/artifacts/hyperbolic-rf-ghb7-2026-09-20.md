# GHB7: localizing flexible HS instability to single expanding blocks

Date: 2026-09-20. Written proof; not Lean-certified. The residual-finiteness
problem and GHB7 flexible HS stability remain open.

## Result and provenance

Let Gamma be a finitely presented Kazhdan group. Subject to the accepted
Liu Theorem 5.1 interface in
`quotient-gap-gives-large-scalar-expanding-blocks`, Gamma is flexibly
Hilbert--Schmidt stable if and only if its approximate representations
with a fixed positive scalar conjugation gap are flexibly roundable,
**using a doubled presentation**. If stability fails, failure is already
witnessed by one sequence of such blocks, with a single gap c>0 and
dimensions tending to infinity.

This is a reduction, not a rounding theorem. In particular it does not
show that GHB7 is stable or produce a non-residually-finite hyperbolic
group. It uses Liu's block decomposition, not merely commutant
internality. The doubled presentation is essential to the actual input.

Analytic input: Jihao Liu, *Nonhyperlinear groups exist*, 2026-09-20,
Theorem 5.1, as recorded and cross-reviewed in
`research/artifacts/liu-theorem-five-assembly-cross-review-2026-09-20.md`.
The present localization and assembly argument is elementary once that
input is supplied. No independent priority claim is made.

## 1. Exact definitions

Fix a finite presentation Gamma=<s_1,...,s_h | R>. Its doubled
presentation has generators s_j^+,s_j^- and relators

    R^dbl = {r(s_1^+,...,s_h^+) : r in R}
            union {s_j^+(s_j^-)^-1 : 1<=j<=h}.

These presentations define the same group. For a tuple
V=(V_1^+,V_1^-,...,V_h^+,V_h^-) in U(d)^(2h), put

    def(V) = max_{r in R^dbl} ||r(V)-I||_(2,d).

All matrix 2-norms are normalized by the dimension indicated. Its
scalar gap is at least c if, for every X in M_d,

    (8h)^-1 sum_{j,sign} ||[V_j^sign,X]||_(2,d)^2
       >= c ||X-tr_d(X)I||_(2,d)^2.                    (SG)

For d=1 this condition is vacuous and causes no problem. Notice that
(SG) implies the exact common commutant of the doubled tuple is scalar.
It does not assert that the tuple is a representation.

Let Q(V) be the infimum over all D>=d and genuine representations
pi:Gamma->U(D), with the standard compression P:C^D->C^d, of

    max { (D-d)/d,
          max_{j,sign} ||V_j^sign-P pi(s_j) P*||_(2,d) }.

Conjugating a representation allows any isometric inclusion of C^d
instead of the standard one. The infimum need not be attained. It is
finite: the trivial d-dimensional representation gives Q(V)<=2.

The **expanding-block rounding condition** is:

    For every c>0 and gamma>0, there exists delta>0 such that
    every dimension d and every doubled tuple satisfying (SG)
    and def(V)<delta have Q(V)<gamma.                  (EBR)

Equivalently, for every fixed c>0, every sequence satisfying (SG) and
def(V_n)->0 has Q(V_n)->0. This equivalence is a direct contraposition:
if the uniform delta fails, choose a violating tuple with defect<1/n.
There is no uniformity requirement as c decreases to zero.

## 2. Stability implies EBR

Suppose flexible HS stability holds and (EBR) fails. Choose a fixed c,
a gamma>0, and tuples V_n with def(V_n)->0 but Q(V_n)>=gamma.
The plus tuples asymptotically satisfy every defining relator, so they
give an asymptotic representation of Gamma by fixing word representatives.
Indeed every null word is a finite product of conjugates of defining
relators, and telescoping bounds its 2-norm defect by a finite sum of
the defining defects. Stability rounds these plus tuples. The doubled
equality relators give ||V_j^+-V_j^-||_2->0, so the same representations
round the minus tuples. Hence Q(V_n)->0, contradiction. No use of (SG)
is needed in this direction.

## 3. EBR implies stability

Suppose stability fails. By the same finite-presentation argument there
are tuples U_n=(U_1,n,...,U_h,n), with all relator defects tending to
zero, whose flexible rounding cost is at least some eta>0 for every n.
Discarding a finite initial segment if necessary, assume 0<eta<=1.

Fix a free ultrafilter omega. In the tracial ultraproduct the U_j,n
give a genuine homomorphism of Gamma. Property (T), applied to its
conjugation representation on L^2, gives the quotient spectral gap
required by Liu Theorem 5.1.

Choose epsilon>0 with 2 sqrt(epsilon)<eta/4, and choose
0<gamma<eta/4. These choices are made **before** using Liu's theorem.
That theorem gives a fixed c=c(epsilon)>0, orthogonal projections
R_0,n,...,R_m(n),n summing to I, and unitaries Z_j,n^+,Z_j,n^-
reducing all these projections, such that

    sum_{j,sign} ||Z_j,n^sign-U_j,n||_(2,d_n)^2 ->_omega 0,
    lim_omega rank(R_0,n)/d_n <= epsilon,

and every nonzero retained block i>=1 satisfies (SG), with the same c,
in its own normalized trace. The number and dimensions of blocks need
not be bounded. The discarded block i=0 has no gap requirement.

For a word w of length L in unitary variables,

    ||w(A)-w(B)||_2 <= sum over its L letters of
                       ||corresponding A letter-B letter||_2.

This also holds for inverse letters. Thus every doubled relator of Z
has 2-norm defect tending to zero along omega. If Z_i,n is the tuple
on a nonzero retained block, and w_i,n=rank(R_i,n)/d_n, then

    A_n := sum_{r in R^dbl} ||r(Z_n)-I||_(2,d_n)^2 ->_omega 0,
    sum_{i>=1} w_i,n def(Z_i,n)^2 <= A_n.             (1)

This calculation is weighted by physical block dimensions, not by the
number of blocks.

Apply (EBR) for this fixed c and gamma, obtaining delta>0. Call block
i>=1 good if def(Z_i,n)<delta and bad otherwise. By (1),

    sum_{i bad} w_i,n <= A_n/delta^2 ->_omega 0.      (2)

Every good block has an actual genuine representation pi_i,n in
dimension D_i,n>=rank(R_i,n) with inflation and all doubled-generator
compression errors <gamma. This follows from Q<gamma even if Q's
infimum is not attained. On all other original block dimensions use
the trivial representation. Form the direct sum of these genuine
representations, identifying each original block with its chosen
compression subspace. This gives a genuine pi_n:Gamma->U(D_n) and

    (D_n-d_n)/d_n <= gamma.

Let q_n be the total original dimension fraction of discarded and bad
blocks. Equations (1)-(2) give lim_omega q_n<=epsilon. Squared normalized
HS errors add across blocks. On a good block the error is <gamma;
on an unrounded block it is <=2. Consequently, for each generator,

    ||Z_j,n^+-P pi_n(s_j)P*||_(2,d_n)
       <= sqrt(gamma^2+4q_n) <= gamma+2 sqrt(q_n).

After adding ||U_j,n-Z_j,n^+||_2, the ultralimit of the error is at
most gamma+2 sqrt(epsilon)<eta/2. The relative inflation is <=gamma<eta.
Thus on an omega-large set the rounding cost of U_n is <eta,
contradicting its stipulated lower bound. This proves stability.

The proof never sends epsilon to zero while retaining c. It fixes
epsilon small enough for one alleged macroscopic failure, and uses
the corresponding fixed gap once. Nor does it infer a gap for Z^+
alone: both copies are retained throughout the use of (EBR).

## 4. A failure is carried by growing single blocks

If stability fails, Sections 2-3 show that (EBR) fails. Therefore
there are c>0, gamma>0 and doubled tuples V_n such that

    scalar gap(V_n)>=c,   def(V_n)<1/n,   Q(V_n)>=gamma. (3)

Their dimensions tend to infinity, after passing to a subsequence
if necessary; in fact every bounded-dimension subfamily is finite.
To check this, if infinitely many dimensions were <=B, a subsequence
would have one fixed dimension d. Compactness of U(d)^(2h) gives a
convergent further subsequence. Its limit satisfies every doubled
relator exactly and therefore is a genuine representation in the
same dimension. That fixed limit representation rounds the converging
tuples with no padding, contradicting Q>=gamma. The limit's scalar
commutant is not needed for this argument.

Thus unbounded numbers of summands or multiplicity spaces are not a
necessary source of instability: one can select one uniformly
expanding, scalar-commutant tuple per coordinate. The scalar commutant
is a coordinate statement about the doubled approximate tuple. No
assertion of finite-dimensional genuine irreducibility is substituted
for it, and no assertion about the ultraproduct's factor type is needed.

## 5. Specialization and what still needs proving

For G=G_HB2(7), take s=(a,b,c) and its established finite presentation.
There are six doubled generators and the energy in (SG) has denominator
24. The finite relator list consists of the existing eleven relators
in a^+,b^+,c^+, plus the three copy-equality relators. By the established
one-edge reduction, (EBR) for this presentation is equivalent both to
flexible HS stability and to one-edge holonomy absorption.

This is a useful new narrow frontier: prove dimension-uniform rounding
of six-unitary scalar expanders satisfying these fourteen relators
approximately, or exhibit a fixed-gap sequence violating it.

The finite vertex representation tables do not solve this frontier.
If one first rounds the vertex restrictions, the resulting perturbation
is controlled in normalized HS norm, which need not preserve the scalar
gap against arbitrary HS-normalized witnesses. A gap-preserving vertex
rounding lemma, or a direct attack on the six-unitary presentation,
would be needed before combining that reduction with block expansion.

Likewise commutant internality controls commuting operators; (EBR)
requires correction of group relators. The proof above supplies no
mechanism for that correction. Degree-two deformation obstructions
remain relevant even though there are no nontrivial coordinate
multiplicity projections in a scalar-expanding tuple.

The independently checked fence
`hrf-audit-projective-internality-does-not-round` is stronger: known
Kazhdan central-cover examples admit nonroundable scalar-expanding
projective models with vanishing operator-norm defects. Thus scalar
expansion alone cannot imply rounding for arbitrary Kazhdan groups.
The GHB7-specific exclusion below removes that globally scalar
projective subclass for this ambient group, while leaving nonscalar
defects and projective models of finite-index subgroups open.

## 6. Scope correction for the one-edge description

With rho_0 and the two other vertex unitary-equivalence classes held
fixed, conjugations in the commutants of rho_0(b) and rho_0(a) preserve
the two already aligned edges. This is a useful sufficient restricted
search. The actual HA statement also permits perturbing rho_0, changing
vertex multiplicities, and flexible compression. No equivalence between
HA and that frozen-vertex restricted search has been proved here.
The wording that commutant conjugations are the only remaining freedom
should not be read as such an equivalence.

## 7. Finite Schur multiplier removes small scalar projective defects

The qualitative projective-rounding phenomenon is already recorded in
`finite-multiplier-projective-models-round-strictly` and its more general
finite-realizable-multiplier variant. The following is an independent
finite-presentation proof of the scalar-relator interface used below;
it is not claimed as a new general rounding principle. The new GHB7
content is the integral vertex-sum calculation and explicit 2401 bound
in Section 8.

**General theorem.** Let Gamma=<s_1,...,s_h | r_1,...,r_m> be finitely
presented with H_2(Gamma;Z) finite. Suppose U_n in U(d_n)^h satisfy

    r_l(U_n)=lambda_l,n I,    lambda_l,n in T,
    max_l |lambda_l,n-1| -> 0.

Then there are scalars alpha_j,n->1 such that alpha_j,n U_j,n are
the generator images of genuine representations of Gamma in the
same dimensions, for all sufficiently large n. The corrections tend
to zero even in operator norm. The scalar-relator hypotheses are exact.

**Proof.** Write F for the free group on the generators and N for
the normal closure of the relators. A tuple U_n gives a homomorphism
F->U(d_n). Since every defining relator has scalar image, every element
of N has scalar image, and conjugation by F does not change that image.
Thus it defines a character chi_n:A=N/[F,N]->T.

The abelian group A is finitely generated by the classes of the m
defining relators. The hypothesis says chi_n tends to the trivial
character on each generator, hence on every fixed element of A.
Hopf's exact sequence is

    0 -> H_2(Gamma;Z) -> A -> F_ab=Z^h -> Gamma_ab -> 0. (4)

This standard input was checked against Clara Loeh's
[*Group Cohomology*, Theorem 1.5.1](https://loeh.app.uni-regensburg.de/teaching/grouphom_ss19/lecture_notes.pdf)
and its low-degree exact sequence.

Let K=ker(A->Z^h), the finite subgroup in (4). On each element of K,
chi_n has values in one finite set of roots of unity and tends to 1.
As K is finite, chi_n|K is trivial for all sufficiently large n.
Consequently chi_n descends to a character theta_n of the sublattice
L=image(A->Z^h), tending to 1 on its fixed finite basis.

Choose a Smith basis e_1,...,e_h of Z^h in which L is generated by
q_1 e_1,...,q_k e_k with positive integers q_i. Write
theta_n(q_i e_i)=exp(i t_i,n) with t_i,n->0. The character beta_n of
Z^h defined by beta_n(e_i)=exp(i t_i,n/q_i) for i<=k and beta_n(e_i)=1
otherwise extends theta_n and tends to 1 on every fixed element.
Twisting F->U(d_n) by beta_n^-1 kills N exactly. Its images of the
original generators are alpha_j,n U_j,n with alpha_j,n->1. This
factors through Gamma and proves the assertion.

If Gamma is finitely presented and b_2(Gamma;Q)=0, the finite-multiplier
hypothesis follows: A is finitely generated, so its subgroup H_2 is
finitely generated, and rational vanishing makes it torsion and finite.
No Kazhdan hypothesis is needed in this general theorem.

## 8. The multiplier of GHB7 and an explicit rounding threshold

For G=G_HB2(7), the triangle-of-finite-groups structure gives the
stronger integral statement

    H_2(G;Z) ≅ H_2(X_0;Z) direct-sum H_2(X_1;Z)
                             direct-sum H_2(X_2;Z).    (5)

The isomorphism is induced by the three vertex inclusions. In particular
2401 H_2(G;Z)=0, since |X_0|=343 and |X_1|=|X_2|=2401.

**Proof of (5), including the spectral-sequence boundary.** The
established CCKW structure provides a contractible, two-dimensional
G-complex Y with the triangle as strict fundamental domain, no
inversions, trivial face stabilizer, cyclic order-seven edge
stabilizers, and vertex stabilizers X_i. Its integral equivariant
homology spectral sequence is

    E^1_(p,q)=direct-sum over p-cell orbits sigma of H_q(G_sigma;Z)
           => H_(p+q)(G;Z),

with stabilizer-inclusion maps, carrying the cellular orientation
signs. Only columns p=0,1,2 occur. In total degree two:

- E^2_(0,2)=direct-sum_i H_2(X_i;Z), because cyclic edge groups have
  H_2(C_7;Z)=0.
- E^2_(1,1)=0. Its possible numerator is the kernel of
  direct-sum_edges H_1(C_7;Z) -> direct-sum_vertices H_1(X_i;Z).
  At each vertex the two incident edge classes form a basis of
  H_1(X_i;Z)=(Z/7)^2, by the established split-abelianization node.
  Therefore the component at any vertex forces the coefficients of
  both its incident edges to vanish; the whole map is injective.
- E^2_(2,0)=0, because the q=0 row is exactly the cellular chain
  complex of a filled triangle.

The sole possible higher differential entering E^2_(0,2) would be
d^2:E^2_(2,1)->E^2_(0,2). Its source is zero because the face
stabilizer is trivial and H_1(1;Z)=0. Higher incoming differentials
have p>=3 and hence zero source. There are no outgoing differentials
from column zero. Thus (5) follows from the filtration on H_2; the
other two associated-graded terms in that degree are zero, so there
is no extension ambiguity. Positive integral homology of a finite
group is killed by the group's order, by transfer from the trivial
subgroup. This proves the stated exponent bound.

**Explicit scalar-relator rounding.** Let U=(A,B,C) be unitaries in
any dimension, and suppose every one of the eleven defining relators
of G evaluates to a scalar lambda_r I. Put

    delta=max_r |lambda_r-1|,   delta_0=2 sin(pi/2401).

If delta<delta_0, there is a genuine representation pi of G in the
same dimension with

    max_{s in {a,b,c}} ||pi(s)-U_s||_op <= (pi/14) delta. (6)

The same bound holds in normalized HS norm.

Indeed each of the eight iterated-commutator relators lies in [F,F].
Its class in N/[F,N] lies in the kernel in (4), hence is killed by
2401 by (5). Its scalar image is a 2401st root of unity. The closest
nontrivial such root to 1 has distance delta_0. Thus all eight
commutator relators are already exactly satisfied.

Write A^7=exp(i t_a)I, B^7=exp(i t_b)I, C^7=exp(i t_c)I with each
t_s in [-pi,pi]. Replace U_s by exp(-i t_s/7)U_s. All three seventh
powers are then I. Scalar changes leave every iterated commutator
unchanged, so all eleven relators hold. Finally

    |exp(-i t/7)-1| <= |t|/7
        <= (pi/14)|exp(i t)-1|

for |t|<=pi, proving (6). This bound is independent of the dimension.

**Doubled subclass.** If all fourteen doubled relators are exactly
scalar and their maximum defect delta tends to zero, apply (6) to
the plus tuple. The copy-equality relators give
||V_s^+-V_s^-||_op<=delta. Hence all six entries round in the same
dimension with errors at most (1+pi/14)delta. Thus the open expanding
block criterion is proved on its globally scalar-relator subclass;
no expansion hypothesis is needed for that subclass.

**Boundary.** The congruence kernel H has b_2(H;Q)>0, so (5)-(6) do
not apply to it. Inducing projective models of H to G may produce
matrix-valued, block-scalar relator defects rather than globally scalar
ones. Nor does an approximately scalar relator necessarily become an
exactly scalar relator by a small correction. Neither step has been
proved here. The actual HA and scalar-expander rounding problems remain
open on these nonscalar defects.

## 9. Independent review record

On 2026-09-20 the campaign's stability-audit agent independently checked
Sections 1-4 against the exact accepted Liu interface and returned
PASS conditional on that named analytic input. The review checked the
fixed-epsilon order of quantifiers, doubled generators, weighted Markov
selection, dimension inflation and compression bounds, and the
bounded-dimension compactness exclusion.

Both the stability-audit agent and the coordinating root agent
independently checked Sections 7-8 and returned PASS. The root checked
the actual eleven-relator presentation as well as the Hopf kernel,
all total-degree-two spectral-sequence terms, the incoming d2 source,
finite-group transfer exponent, and the pi/14 correction estimate.
The audit agent additionally checked the doubled-tuple bound and the
finite-index/nonscalar boundary. These are written mathematical reviews,
not formal proof-assistant verification or a claim that HA is solved.

## 10. Exact central relators also round in normalized HS norm

There is a useful strengthening of Section 8 that permits large scalar
defects on a small invariant summand. It requires centrality of the
relator matrices exactly, rather than global scalarity or approximate
centrality.

**Theorem.** Let U=(A,B,C) in U(d)^3. Suppose that every defining
relator r(U) commutes with A, B and C. Define the normalized HS defect

    delta=max over eleven relators r of ||r(U)-I||_(2,d),
    delta_0=2 sin(pi/2401).

Then a genuine representation pi:GHB2(7)->U(d) exists with

    ||pi(s)-U_s||_(2,d)^2
       <= (pi/14)^2 ||U_s^7-I||_(2,d)^2
          + (4/delta_0^2) sum over eight commutator relators r
                                  ||r(U)-I||_(2,d)^2.       (7)

In particular the generator errors are <=C delta, where
C=sqrt((pi/14)^2+32/delta_0^2), independent of d. There is no
smallness requirement on delta for the inequality, and no padding.

**Proof.** The eleven relator matrices are commuting normal unitaries:
each commutes with the generators, hence with every word in them.
Decompose C^d into their simultaneous eigenspaces. Each such subspace
reduces all three generators, and on it every defining relator is
scalar. By the Hopf-kernel argument of Section 8, each commutator
relator's phase on every nonzero subspace is a 2401st root of unity,
irrespective of its distance from 1.

Let p be the projection onto the sum of simultaneous eigenspaces on
which all eight commutator phases equal 1. Its complement q reduces
the generators. Every sector of q has at least one nontrivial
commutator phase and therefore at least one commutator defect of
modulus >=delta_0. Summing by original physical dimensions gives

    tr_d(q) <= delta_0^-2 sum over commutator relators r
                                      ||r(U)-I||_(2,d)^2.   (8)

On each sector of p correct the three seventh powers by the scalar
roots from Section 8. Those corrections preserve every commutator,
so they yield genuine G representations on p. On q choose the trivial
representation in its original dimension. Take their direct sum.

For generator s, the squared error on p is bounded by
(pi/14)^2 tr_d(p|U_s^7-I|^2), by the pointwise scalar sine bound.
On q the squared error is at most 4 tr_d(q), since both matrices are
unitary. Orthogonality adds these squared errors, and (8) proves (7).
The proof uses rank weights and never bounds the number of eigensectors.

For the doubled presentation it suffices that the eleven plus relators
are exactly central with respect to the plus generators and that the
plus-relator and copy-equality defects tend to zero in normalized HS norm. Apply (7)
to the plus tuple and use the triangle inequality for the minus tuple.
The equality defects need not themselves be central in this extension.

**Scope of the obstruction.** A possible instability witness must have
relator defects that are not exactly central in the algebra of its
generators (unless it violates another stated hypothesis). Merely being
block scalar in a decomposition is weaker: if generators permute those
blocks, the relators need not commute with them. Such induced models
are not covered by (7). Nor does approximate centrality imply exact
centrality after a controlled correction. Scalar expansion does not
fill that gap; when exact centrality and scalar expansion both hold,
the central relators are already scalar.

Section 10 and its graph nodes were independently reviewed by both
the campaign root and stability-audit agents on 2026-09-20, with PASS.
The audit checked exact centrality, invariant-sector decomposition,
the unrestricted root-of-unity argument, dimension-weighted bad mass,
the same-dimension squared-error inequality, and the doubled extension.
