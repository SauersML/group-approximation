---
rg: 2
id: stw22-matrix-carrier-bott-induction-proof
kind: route
title: Induct carriers over all skeleta and absorb every finite-degree matrix obstruction
target: stw22-matrix-weighted-copy-uniform-finite-degree-fillings
requires:
  - stw22-matrix-weighted-copy-uniform-s2-fillings
  - stw22-matrix-weighted-copy-codimension-two-uniform-s4-fillings
  - stw22-multicopy-fibres-collapse-and-zero-slack-obstructs-lc1
artifacts:
  - research/artifacts/stw22-matrix-finite-degree-carrier-induction-audit-2026-08-31.md
---

All traces are normalized.  Fix j>=2 and abbreviate

    t=floor((j-1)/2),   r=floor(j/2),
    A=t(t+1)/2,         C_j=j+1+A+r.                       (BI-1)

Let q have rank k in M_n and put c=n-k.  The unitary fibration

    U(c) -> U(n) -> St_n(q)=V_k(C^n)

and the stable range for U(c)->U(n) show that V_k(C^n) is
2c-connected.  We assume 2c>=j and prove a quantitative version for
j-spheres.

## 1. Defect localization and the initial carrier

Translate the centre to q.  Given

    v:S^j->St_n(q),       A_x=v(x)-q,
    sup_x ||A_x||_2<delta,

fix 0<kappa<1/20 and set

    K=floor(4n delta^2/kappa^2).                           (BI-2)

Triangulate S^j so finely that

    ||A_x-A_i||<kappa/2                                  (BI-3)

in operator norm whenever x and the original vertex i lie in the same
closed simplex.  This uses only uniform continuity for the fixed M_n and
the finite-n equivalence of the operator and normalized Hilbert-Schmidt
norms.  At each original vertex set

    p_i=1_((kappa/2),infinity)(|A_i|).

Then rank(p_i)<=K.  If K=0, (BI-3) makes the entire defect
operator-norm-small and the direct-rotation homotopy contracts v with the
bounds below.

Assume K>=1 and put L=(j+1)K.  If

    k<=L+A+r,                                             (BI-4)

ordinary j-connectivity supplies a filling.  Every point of the whole
Stiefel manifold is at normalized distance at most 2sqrt(k/n) from q,
and (BI-2)--(BI-4) give

    2sqrt(k/n)<=4sqrt(C_j) delta/kappa.                   (BI-5)

We may therefore suppose k>=L+A+r+1.

Pass to the barycentric subdivision and write X^(d) for its d-skeleton.
For each original simplex sigma let P_sigma be the join of the p_i over
its vertices.  Thus

    rank(P_sigma)<=(dim(sigma)+1)K<=L.

At the barycentre of sigma choose an L-plane E_sigma containing P_sigma.
For an edge sigma_0<sigma_1, join its endpoint planes inside the
Grassmannian of L-planes containing P_(sigma_0).  For a barycentric
triangle sigma_0<sigma_1<sigma_2, its entire boundary lies in the
Grassmannian containing P_(sigma_0); fill there, using simple
connectivity of complex Grassmannians.  This constructs a rank-L carrier
E on X^(2).  On every barycentric cell it contains P_sigma for its least
face sigma, and therefore retains at least one hard carrier from a nearby
original vertex.  Equations (BI-3) and the spectral cutoff give

    ||A_x(q-E_x)||<kappa.                                (BI-6)

## 2. Skeleton induction

We use two standard finite-range bundle facts, including their rank
conditions.

First, if a complex rank-s bundle xi lies over a finite 2h-dimensional
CW complex and s>=h, then

    xi ~= D_h direct-sum 1^(s-h)                         (BI-7)

for a rank-h bundle D_h.  Indeed, the unit sphere of a rank-ell complex
bundle is (2ell-2)-connected, so obstruction theory successively gives
nonzero sections while ell>h.

Second, stable triviality of a complex rank-u bundle on a
2h-dimensional complex implies actual triviality when u>h.  Equivalently,
the finite classifying map BU(u)->BU is already in the required stable
range.  We also use the complementary formulation: the map

    Gr_u(C^(u+s)) -> BU(s)                               (BI-8)

which classifies the complementary s-plane is 2u-connected.

Inductively suppose a carrier of rank

    R_(h-1)=L+h(h-1)/2                                  (BI-9)

has been constructed on X^(2h), contains the prescribed least-face
carrier on every cell, and satisfies (BI-6).  This is the preceding
construction when h=1.  Its complement xi=q-E has rank
s=k-R_(h-1).  The large-source inequality implies s>=h.  Split xi as in
(BI-7), regard D_h as an orthogonal subprojection, and promote

    E_h=E+D_h,          R_h=L+h(h+1)/2.                 (BI-10)

Over X^(2h), q-E_h is trivial.  Thus E_h is stably trivial, and it is
actually trivial because R_h>h.

Now extend E_h cell by cell through X^(min(2h+2,j)).  A barycentric
d-cell is indexed by a chain

    sigma_0<sigma_1<...<sigma_d.

Since dim(sigma_0)<=j-d,

    rank(P_(sigma_0))<=(j-d+1)K,                        (BI-11)

so the variable tautological rank in its containing Grassmannian is at
least dK.  Moreover

    k-R_h>=r+1>=h+1                                    (BI-12)

for every h<=t.  On a (2h+1)-cell the boundary is S^(2h).
The variable tautological bundle is stably trivial (the fixed
P_(sigma_0) and E_h are trivial), has rank greater than h, and is
therefore trivial.  By (BI-8), or symmetrically by the tautological
classifying map, this is the complete obstruction: the boundary map is
null inside the same containing Grassmannian.  Extending there preserves
both its least-face carrier and (BI-6).

On a (2h+2)-cell, both the variable tautological and complementary ranks
are at least h+1.  The stable unitary exact sequence gives

    pi_(2h+1)(Gr_u(C^(u+s)))=0                          (BI-13)

in these ranks, so its boundary also fills inside the same containing
Grassmannian.  This proves the induction step.

Run (BI-10) for h=1,...,t.  The result is a carrier on all of S^j of
rank

    R_0=L+A                                             (BI-14)

and satisfying (BI-6).  For even j the last extension is the
2r-skeleton after h=r-1; for odd j it is already obtained after h=r.
The construction is coherent on common faces because every extension is
made in the Grassmannian determined by that face's least original
simplex.

## 3. Localization and the final obstruction

Direct rotation of the good part gives a homotopy, within

    delta+10kappa                                       (BI-15)

of q, to

    v'(x)=q-E_x+W_x,
    W_x^*W_x=E_x,       W_xW_x^* orthogonal to q-E_x.   (BI-16)

Let Z_R be the space of pairs occurring in (BI-16) with carrier rank R.
Projection to E gives a fibration

    V_R(C^(R+c)) -> Z_R -> Gr_R(C^k).                   (BI-17)

The Stiefel fibre is 2c-connected.  Since 2c>=j,

    pi_j(Z_R) ~= pi_j(Gr_R(C^k)).                       (BI-18)

This uses the vanishing of both pi_(j-1) and pi_j of the fibre.

If j=2r+1 is odd, the carrier rank R_0 and complement rank
s=k-R_0 are both at least r+1.  In the homogeneous-space exact sequence,
the stable maps

    pi_(2r+1)(U(R_0) x U(s)) -> pi_(2r+1)(U(k))

are addition Z x Z -> Z and hence surjective, while the adjacent even
unitary groups vanish.  Therefore

    pi_(2r+1)(Gr_(R_0)(C^k))=0.                         (BI-19)

Equations (BI-18)--(BI-19) fill the localized sphere.

Let j=2r be even.  The complement xi=q-E over S^(2r) has rank s>=r+1.
Apply (BI-7) once more:

    xi ~= D_r direct-sum 1^(s-r).                       (BI-20)

Promote both coordinates by this rank-r block,

    E'=E+D_r,            W'=W+D_r.                     (BI-21)

The represented Stiefel point is exactly unchanged:

    q-E'+W'=q-E-D_r+W+D_r=q-E+W.                        (BI-22)

The remaining complement q-E' is the trivial rank-(s-r) bundle.  This
is the complete finite-Grassmannian obstruction, not merely a formal
appeal to vanishing even homotopy of a unitary group.  Indeed, E' has
rank R'=R_0+r>r, and the complementary classifying map

    Gr_(R')(C^(R'+s-r)) -> BU(s-r)                      (BI-23)

is 2R'-connected.  The image of the promoted S^(2r) in BU(s-r)
classifies the trivial bundle, so (BI-23) forces the promoted
Grassmannian sphere itself to be null.  This rules out all unstable
torsion, including the CP^1-type exceptions.  Equation (BI-18), with
R', then fills the unchanged localized Stiefel sphere.

## 4. Uniform constants

In either parity the final carrier rank is at most

    R_0+r=L+A+r<=C_j K                                 (BI-24)

because K>=1.  Any point in an arbitrary localized filling is therefore
within

    2sqrt(R/n)<=4sqrt(C_j) delta/kappa                  (BI-25)

of q.  Choose

    epsilon_0=min(epsilon,1),
    kappa=epsilon_0/40,
    delta=epsilon_0^2/(2560 C_j).                       (BI-26)

The small-source estimate (BI-5), the direct-rotation collar (BI-15),
and the localized estimate (BI-25) all lie inside the epsilon-ball.
This proves the projection modulus.

## 5. Weights and copies

Let a be nonzero, p=supp(a), and suppose c=n-m rank(p) satisfies
2c>=j.  Polar decomposition and the exact multicopy isometry identify
the topology of the weighted frame fibre with V_(m rank(p))(C^n).

For a small weighted j-sphere put

    eta=(epsilon_0/12)^2,
    p_h=1_[eta,1](a),        p_l=p-p_h.

The high polar frame still has at least c unused target dimensions.
Applying the projection theorem with output radius epsilon_0/3 requires
weighted input at most

    sqrt(eta) rho_(j,St)(epsilon_0/3)
      =epsilon_0^3/(276480 C_j).                        (BI-27)

Fill the high frame over B^(j+1).  Its complement bundle is trivial over
the ball.  The boundary low frame maps to a complex Stiefel manifold
with unused rank at least c; its pi_j vanishes because 2c>=j, so it
extends.  The universal low weighted estimate costs at most
2sqrt(eta)<=epsilon_0/6.  This proves (FD-2).  The homogeneous-space
calculation at the start gives global j-connectivity.  The case a=0 is
a singleton.

## 6. Sharpness and the trace range

Fix c>=1, n>c, k=n-c, and let q be the standard rank-k projection.
Inside

    B=span{e_1,e_(n-c+1),...,e_n} ~= C^(c+1)

define, for x in its unit sphere S^(2c+1),

    Phi_(n,c)(x)=x e_1^* + sum_(i=2)^k e_i e_i^*.       (BI-28)

This is a based sphere in St_n(q), and

    ||Phi_(n,c)(x)-q||_2<=2/sqrt(n).                    (BI-29)

The forget-first-vector fibration has fibre (BI-28):

    S^(2c+1) -> V_k(C^n) -> V_(k-1)(C^n).

The base has codimension c+1 and is (2c+2)-connected, so its long exact
sequence makes the fibre inclusion an isomorphism on pi_(2c+1).
Thus (BI-28) generates pi_(2c+1)=Z.  With m=1 and a=q, its slack c/n is
strictly positive; fixed-c generators shrink as n grows.  This proves
the asserted sharpness.

Finally, if p has positive rank and m tau(p)<=1/2, then

    n>=2m rank(p),       c=n-m rank(p)>=m rank(p)>=m.

Hence m>=ceil(j/2) implies 2c>=j, as claimed.
