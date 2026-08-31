---
rg: 2
id: stw22-matrix-four-sphere-bott-cancellation-proof
kind: route
title: Extend a five-carrier field and absorb the localized Bott class in rank two
target: stw22-matrix-weighted-copy-codimension-two-uniform-s4-fillings
requires:
  - stw22-matrix-weighted-copy-codimension-two-uniform-s3-fillings
artifacts:
  - research/artifacts/stw22-matrix-lc4-bott-cancellation-audit-2026-08-31.md
---

All traces are normalized.  Let q have rank k and put c=n-k>=2.  The
fibration

    U(c)->U(n)->St_n(q)=V_k(C^n)

shows that St_n(q) is 2c-connected, hence 4-connected.  We prove a
dimension-free quantitative form for four-spheres.

## 1. The carrier through the three-skeleton

After left-translating the centre to q, let

    v:S^4->St_n(q),       A_z=v(z)-q,
    sup_z ||A_z||_2<delta.

Fix 0<kappa<1/20 and put

    K=floor(4n delta^2/kappa^2).                        (F4-1)

Choose a triangulation so fine in the fixed matrix operator norm that A_x
and A_i differ by less than kappa/4 whenever x and the original vertex i
belong to one closed four-simplex.  Let

    p_i=1_((kappa/2),infinity)(|A_i|).

Then rank(p_i)<=K and ||A_i(q-p_i)||<=kappa/2.

If K=0, direct rotation contracts the sphere.  If K>0 and k<=5K,
ordinary 4-connectivity gives a filling, and every point of the whole
Stiefel space lies within

    2sqrt(k/n)<=2sqrt(20)delta/kappa<9delta/kappa       (F4-2)

of q.

Assume k>=5K+1.  Enlarge the p_i to rank K and set L=5K.  On the
barycentric two-skeleton Y proceed as follows.  For every original simplex
sigma let

    P_sigma=join_(i a vertex of sigma)p_i.

Because dim(sigma)<=4, rank(P_sigma)<=5K=L.  Choose a rank-L projection
E_sigma containing P_sigma at its barycentre.  On a barycentric edge
sigma<tau connect E_sigma to E_tau inside the Grassmannian of rank-L
planes containing P_sigma.  The boundary of a barycentric triangle

    sigma_0<sigma_1<sigma_2

lies in the Grassmannian containing P_(sigma_0); fill it there.  These
complex Grassmannians are simply connected, so the choices glue to a
rank-L projection e on Y.  Every point retains a carrier from a nearby
original vertex, and hence

    ||A_x(q-e_x)||<kappa       (x in Y).                (F4-3)

The complement q-e has rank at least one over the finite two-dimensional
CW complex Y.  It splits as its determinant line plus a trivial bundle.
Choose a line d inside q-e with

    c_1(d)=-c_1(e),

and put E=e+d, of rank

    R_0=5K+1.                                           (F4-4)

Now c_1(E)=0 on Y.  On the boundary of each barycentric three-cell, E
takes values in the Grassmannian of rank-R_0 planes containing the carrier
attached to its least original face.  The tautological c_1 detects pi_2
of that Grassmannian, so the boundary fills inside the same containing
Grassmannian.  This extends E over the barycentric three-skeleton and
preserves (F4-3).

A top barycentric four-cell is a chain

    vertex i < edge < face < tetrahedron < four-simplex.

Every point of its boundary contains p_i.  The boundary carrier therefore
maps to

    G_(R_0)(p_i) ~= Gr_(R_0-K)(C^(k-K)).                (F4-5)

Here R_0-K=4K+1>=5.  The group pi_3 of (F4-5) is zero: the point cases are
trivial, the complementary-rank-one case is a complex projective space
of complex dimension at least five, and in the remaining cases a unitary
block supplies a surjection on pi_3.  Thus E extends over every four-cell
inside (F4-5).  We obtain a rank-R_0 carrier on all of S^4 satisfying

    ||A_z(q-E_z)||<kappa.                               (F4-6)

## 2. Direct rotation and the localized pi_4 obstruction

Direct rotation of the good part gives a homotopy, within

    delta+10kappa                                      (F4-7)

of q, to

    v'(z)=q-E_z+W_z,
    W_z^*W_z=E_z,       W_zW_z^* orthogonal to q-E_z.  (F4-8)

Let Z_r denote the space of pairs in (F4-8) with carrier rank r.  It
fibres over Gr_r(C^k), with fibre V_r(C^(r+c)).  Since c>=2, this fibre
has pi_3=pi_4=0.  Consequently

    pi_4(Z_r) -> pi_4(Gr_r(C^k))                       (F4-9)

is an isomorphism in the ranks used below.

Put s=k-R_0, the rank of q-E over S^4.  If s=0, the Grassmannian base is
a point.  If s=1, it is a complex projective space of complex dimension
R_0>=6 and has pi_4=0.  In either case (F4-9) fills the localized sphere
without further promotion.

Suppose s>=2.  Complex rank-s bundles over S^4 are classified by their
clutching class in pi_3(U(s))=Z.  The inclusion U(2)->U(s) is an
isomorphism on pi_3, so the complement bundle xi=q-E splits as

    xi ~= D plus a trivial bundle of rank s-2,           (F4-10)

where D is a rank-two subbundle carrying its full Bott class.  Regard D
as an orthogonal subprojection and promote

    E'=E+D,       W'=W+D.                              (F4-11)

The represented frame is unchanged:

    q-E'+W'=q-E-D+W+D=q-E+W.                           (F4-12)

Since E plus xi is trivial and H^2(S^4)=0, the Whitney formula gives

    c_2(E')=c_2(E)+c_2(D)=0.                           (F4-13)

For the new Grassmannian base, pi_4 is zero if its complement has rank at
most one, and otherwise is Z detected by the tautological c_2.  Thus the
promoted base sphere is null.  By (F4-9), the promoted pair sphere is null
in Z_(R_0+2).

This includes the unstable c=2 case.  Although pi_4(U(2)) contains
two-torsion, the map pi_3(U(2))->pi_3(U(R_0+2)) is an isomorphism, and the
homotopy exact sequence gives pi_3=pi_4=0 for
V_(R_0)(C^(R_0+2)).  No torsion survives in (F4-9).

## 3. Quantitative bound

The final carrier rank R is either R_0 or R_0+2.  Since K>=1,

    R<=5K+3<=8K<=32n delta^2/kappa^2.                  (F4-14)

Every point of an arbitrary localized filling therefore lies within

    2sqrt(R/n)<=2sqrt(32)delta/kappa<12delta/kappa     (F4-15)

of q.  Choose

    epsilon_0=min(epsilon,1),
    kappa=epsilon_0/40,
    delta=epsilon_0^2/2560.                            (F4-16)

The small-source bound, the direct-rotation collar, and (F4-15) all lie
inside the epsilon-ball.  Gluing the collar to the localized B^5 filling
proves the projection modulus.

## 4. Weights, copies, and global connectivity

Let a be nonzero, p=supp(a), and assume c=n-m rank(p)>=2.  Polar
decomposition and the exact multicopy isometry identify its frame topology
with V_(m rank(p))(C^n).

For a small weighted S^4, use

    eta=(epsilon_0/12)^2,
    p_h=1_[eta,1](a),       p_l=p-p_h.

The high polar frame has at least c unused target dimensions.  Applying
the projection theorem with output radius epsilon_0/3 requires the input

    sqrt(eta) rho_(4,St)(epsilon_0/3)
      =epsilon_0^3/276480.                             (F4-17)

Fill the high frame over B^5.  Its complement bundle is trivial over the
ball.  The boundary low frame maps into a complex Stiefel manifold with
the same unused rank c>=2.  Its pi_4 vanishes, so it extends over B^5.
The universal low weighted estimate is

    sum_j||(T_j-s_(0,j))a^(1/2)p_l||_2^2<=4eta,        (F4-18)

and hence costs at most epsilon_0/6.  This proves the cubic modulus.

The homogeneous space is 4-connected by the opening computation, so each
weighted fibre is globally 4-connected.  If m>=2 and
m tau(p)<=1/2, every nonzero matrix fibre has c>=2 by the rank calculation
in the required degree-three theorem.  Thus the result covers the matrix
branch of the half-slack replication regime used in fibre-gap selection.
