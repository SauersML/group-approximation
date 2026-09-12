---
rg: 2
id: stw22-matrix-three-sphere-carrier-and-su2-obstruction-proof
kind: route
title: Cancel the carrier Chern class on the two-skeleton and isolate the small SU(2) obstruction
target: stw22-matrix-weighted-copy-codimension-two-uniform-s3-fillings
requires:
  - stw22-matrix-weighted-copy-uniform-s2-fillings
  - stw22-multicopy-fibres-collapse-and-zero-slack-obstructs-lc1
artifacts:
  - research/artifacts/stw22-matrix-lc3-codimension-barrier-audit-2026-08-31.md
---

All matrix traces are normalized.  We first settle the topology, then prove
the quantitative codimension-two theorem, transfer it to weights, and
finally exhibit the sharp codimension-one obstruction.

## 1. Exact topology through degree three

Let q have rank k and put c=n-k.  There is a homogeneous-space
identification

    St_n(q) ~= V_k(C^n)=U(n)/U(c).                     (T3-1)

For c>=2, the block inclusion U(c)->U(n) is an isomorphism on pi_1 and
pi_3, and unitary groups have pi_2=0.  The homotopy exact sequence of
(T3-1) therefore gives

    pi_1(St_n(q))=pi_2(St_n(q))=pi_3(St_n(q))=0.       (T3-2)

Thus the Stiefel space is 3-connected.  If c=1 and k>0, the map on pi_1
is still an isomorphism, but pi_3(U(1))=0 and pi_3(U(n))=Z.  Hence

    pi_1=pi_2=0,       pi_3(St_n(q))=Z.                (T3-3)

The case k=0 is a point.

For a nonzero matrix weight a, restriction of a to p=supp(a) has a
bounded inverse.  Polar decomposition is therefore a homeomorphism from
the weighted m-copy fibre onto the space of m orthogonal p-frames.
Relative to one base frame, the exact multicopy identification turns that
space into (T3-1) with k=m rank(p).  The zero weight has singleton fibre.
Consequently (T3-2)--(T3-3) give the stated global topology for every
weighted fibre.

## 2. A rank-4K carrier on the barycentric two-skeleton

Assume c>=2.  As in the degree-two proof, left translation by a unitary
normalizes the centre of a small sphere to q.  Write

    v:S^3->St_n(q),       A_z=v(z)-q,
    sup_z ||A_z||_2<delta.

Fix 0<kappa<1/20 and set

    K=floor(4n delta^2/kappa^2).                       (T3-4)

In the fixed M_n, 2-norm continuity implies operator-norm continuity.
Choose a triangulation of S^3 so fine that A_x and A_i differ in operator
norm by less than kappa/4 whenever x and the original vertex i belong to
one closed tetrahedron.  At every original vertex i let

    p_i=1_((kappa/2),infinity)(|A_i|).

Then

    rank(p_i)<=K,       ||A_i(q-p_i)||<=kappa/2.       (T3-5)

If K=0, (T3-5) and the fine mesh make ||A_x||<3kappa/4
everywhere, so direct rotation contracts the sphere.

Suppose K>0.  If k<=4K, (T3-2) supplies an arbitrary filling, and every
point u of it satisfies

    ||u-q||_2<=2sqrt(k/n)<=8delta/kappa.               (T3-6)

It remains to consider k>=4K+1.  Enlarge every p_i to rank K and put
L=4K.  Let Y be the two-skeleton of the barycentric subdivision.  For an
original simplex sigma, let

    P_sigma=join_(i a vertex of sigma) p_i.

Its rank is at most (dim(sigma)+1)K<=4K.  At the barycentre b_sigma choose
a rank-L projection E_sigma containing P_sigma.

For every barycentric edge b_sigma b_tau with sigma contained in tau,
connect E_sigma to E_tau inside the Grassmannian G_L(P_sigma) of rank-L
planes containing P_sigma.  For a barycentric triangle coming from a
chain

    sigma_0 contained in sigma_1 contained in sigma_2,

its entire boundary lies in G_L(P_(sigma_0)).  This is an ordinary complex
Grassmannian and is simply connected whenever it is not a point.  Fill
the triangle there.  All barycentric edges were chosen once globally, so
adjacent faces agree.  We obtain a continuous rank-L projection e on Y.

Every point of a barycentric face contains all the p_i belonging to the
least original simplex in its chain, hence at least one vertex carrier
from the same fine tetrahedron.  Equations (T3-5) give

    ||A_x(q-e_x)||<3kappa/4<kappa        (x in Y).      (T3-7)

## 3. One determinant line removes every three-cell obstruction

The complement bundle xi=q-e over the finite two-dimensional CW complex
Y has rank k-L>=1 and

    c_1(xi)=-c_1(e).                                   (T3-8)

Every rank-r complex vector bundle over a two-dimensional CW complex is
classified by c_1 and is isomorphic to its determinant line plus r-1
trivial lines.  Thus xi contains a line subbundle d with

    c_1(d)=-c_1(e).                                    (T3-9)

Choose its orthogonal projection and put

    E=e+d,       R=L+1=4K+1.                           (T3-10)

Then E contains e, so (T3-7) remains true, and c_1(E)=0 on all of Y.

A top-dimensional barycentric simplex is a chain

    i contained in edge contained in face contained in tetrahedron.

Every point of its boundary has E>=p_i.  Hence the boundary carrier is a
map into

    G_R(p_i) ~= Gr_(R-K)(C^(k-K)).                     (T3-11)

The first Chern class of the tautological bundle detects pi_2 of this
Grassmannian; in the point cases the group is zero.  The restriction of
c_1(E) to the boundary sphere is zero, so (T3-11) is null-homotopic.
Fill E across that three-cell inside G_R(p_i).  Doing this independently
on every top cell gives a continuous rank-R projection on S^3.  It still
contains a nearby vertex carrier at every point, and therefore

    ||A_x(q-E_x)||<kappa        (x in S^3).             (T3-12)

The determinant-line promotion is global on Y.  No incompatible
cell-by-cell line choices are made.

## 4. Direct rotation and the localized configuration

Put f=q-E, x_z=v(z)f_z, and y_z=f_z.  By (T3-12) the direct-rotation
lemma gives a homotopy in St_n(q), staying within

    delta+10kappa                                      (T3-13)

of q, from v to a localized sphere

    v'(z)=q-E_z+W_z,
    W_z^*W_z=E_z,       W_zW_z^* orthogonal to q-E_z.  (T3-14)

Let Z_R be the configuration space of pairs (E,W) in (T3-14).  It fibres
over Gr_R(C^k), with fibre V_R(C^(R+c)).  Since c>=2, this Stiefel fibre
has pi_3=0.  The base also has pi_3=0 in the present range: K>=1 gives
R=4K+1>=5; if k=R the base is a point, while if k>R the block inclusion
U(R)->U(k) is onto on pi_3.  This explicitly excludes the exceptional
Grassmannian Gr_1(C^2)=CP^1, whose pi_3 is nonzero.  The exact sequence of
the bundle now yields

    pi_3(Z_R)=0.                                       (T3-15)

Fill the localized sphere in Z_R.  Every represented Stiefel point in this
uncontrolled filling differs from q only on a rank-R right support, so

    ||q-E_y+W_y-q||_2
       <=2sqrt(R/n)
       <=2sqrt(20) delta/kappa
       <9delta/kappa.                                  (T3-16)

Here K>=1 and

    R=4K+1<=5K<=20n delta^2/kappa^2.

Choose, with epsilon_0=min(epsilon,1),

    kappa=epsilon_0/40,
    delta=epsilon_0^2/2560.                            (T3-17)

Then (T3-6), (T3-13), and (T3-16) are all smaller than epsilon.
Glue the direct-rotation homotopy on an outer collar of B^4 to the
localized filling.  This proves the quadratic projection modulus.  The
initial left translation transfers the result to a ball about any centre.

## 5. Positive weights and arbitrary copy number

Let a be nonzero, p=supp(a), and assume

    c=n-m rank(p)>=2.                                  (T3-18)

Write a boundary weighted frame as v_j=s_ja^(1/2), fix
epsilon_0=min(epsilon,1), and put

    eta=(epsilon_0/12)^2,
    p_h=1_[eta,1](a),       p_l=p-p_h.

The high polar frame moves by at most eta^(-1/2) times the weighted
distance.  Its total unused target rank is at least c, so the projection
theorem applies in degree three with output radius epsilon_0/3.  The
required weighted input is

    sqrt(eta) rho_(3,St)(epsilon_0/3)
      =epsilon_0^3/276480.                             (T3-19)

Fill the high frame over B^4.  Its range-complement bundle is trivial
because the ball is contractible.  On the boundary, the low polar frame
takes values in the complex Stiefel manifold whose unused target rank is
exactly c>=2.  Its pi_3 vanishes by (T3-2), so it extends over B^4 inside
the moving complement.

Multiply the combined high-low frame by a^(1/2).  The high weighted cost
is at most epsilon_0/3.  For any low extension,

    sum_j||(T_j-s_(0,j))a^(1/2)p_l||_2^2
       <=4m tau(ap_l)
       <=4eta m tau(p_l)
       <=4eta,                                         (T3-20)

so the low cost is at most epsilon_0/6.  This proves the cubic modulus.
Global 3-connectivity follows either from the same construction without
estimates or directly from the homeomorphism in Step 1.

## 6. The small essential SU(2) sphere

For n>=3 put q_n=diag(I_(n-1),0).  Embed SU(2) into the first two
coordinates of U(n), which lie inside q_n, and define

    Phi_n(g)=diag(g,I_(n-2))q_n.                       (T3-21)

The quotient U(n)->U(n)/U(1)=St_n(q_n) induces an isomorphism on pi_3,
because pi_3(U(1))=pi_2(U(1))=0.  The standard SU(2) block represents a
generator of pi_3(U(n)); hence (T3-21) is essential.

Its normalized metric radius is

    ||Phi_n(g)-q_n||_(2,n)^2
      =n^(-1)||g-I_2||_HS^2
      <=8/n,                                           (T3-22)

with equality at g=-I_2.  Given any positive radius, take n large enough
that sqrt(8/n) is smaller.  The resulting sphere has no extension anywhere
in the fibre.  Yet, with m=1 and a=q_n,

    tau(a)=1-1/n,

so it satisfies strict slack with gamma_n=1/n.  This disproves a modulus
uniform jointly over all matrix sizes and all positive amounts of slack.
It does not assert failure for each fixed numerical gamma.

Finally suppose m>=2, a!=0, and m tau(p)<=1/2.  Then
k=m rank(p)>=2 and k<=n/2.  Hence n>=4 and

    c=n-k>=n/2>=2.                                     (T3-23)

Thus the codimension-one sphere cannot occur in the half-slack,
replication-at-least-two matrix regime used by the fibre-gap trace
argument.  The matrix branch is therefore compatible with a possible
dimension-four Michael-selection proof; a corresponding diffuse
degree-three theorem is a separate input.
