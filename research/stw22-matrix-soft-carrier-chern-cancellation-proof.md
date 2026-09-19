---
rg: 2
id: stw22-matrix-soft-carrier-chern-cancellation-proof
kind: route
title: Fill small matrix Stiefel two-spheres by a three-carrier field and one Chern-cancelling line
target: stw22-matrix-weighted-copy-uniform-s2-fillings
requires:
  - stw22-matrix-weighted-copy-uniform-loop-fillings
  - stw22-multicopy-fibres-collapse-and-zero-slack-obstructs-lc1
artifacts:
  - research/artifacts/stw22-matrix-uniform-s2-filling-audit-2026-08-30.md
---

All traces are normalized.  The direct-rotation lemma and the exact
multicopy-to-one-Stiefel isometry are the ones proved in the required
matrix loop package.  We record every new degree-two step.

## 1. Normalize the centre

Let q have rank k<n and let

    v:S^2 -> St_n(q),       sup_z ||v(z)-v_0||_2<delta.

A partial isometry carrying v_0 to q extends across the two equal-rank
orthogonal complements to a unitary.  Left multiplication by this unitary
is an exact 2-isometry.  We may therefore assume v_0=q and put

    A_z=v(z)-q.

Although no dimension-free comparison between operator norm and normalized
2-norm is used, in the one fixed M_n the two norms induce the same
topology.  Thus A is operator-norm continuous.  This fact will choose a
fine triangulation; neither the number nor the mesh of its simplices enters
any estimate.

## 2. A rank-3K carrier over S^2

Fix 0<kappa<1/20 and set

    K=floor(4n delta^2/kappa^2).

Choose a triangulation of S^2 so fine that whenever x and a vertex i lie
in one closed simplex,

    ||A_x-A_i|| < kappa/4.                              (C1)

At every vertex i let p_i be the spectral projection of |A_i| for
(kappa/2,infinity).  Chebyshev gives

    rank(p_i) kappa^2/4 < n delta^2,
    rank(p_i)<=K,       ||A_i(q-p_i)||<=kappa/2.        (C2)

When K>0 and k>=3K+1, enlarge each p_i inside q to rank exactly K and put
L=3K.  We now construct a continuous rank-L projection e_x<=q.

For a projection r<=q, write G(r) for the Grassmannian of rank-L
projections containing r.  It is a complex Grassmannian

    G(r) ~= Gr_(L-rank(r))(C^(k-rank(r))).

It is connected, and it is simply connected whenever it is not a point.
The construction is skeleton by skeleton on the barycentric subdivision.

* At an original vertex i choose E_i in G(p_i).
* At the midpoint of an edge ij choose E_ij containing p_i join p_j.
  Join rank is at most 2K.  Join E_i to E_ij through G(p_i), and join
  E_ij to E_j through G(p_j).
* At the barycentre of a face ijl choose E_ijl containing
  p_i join p_j join p_l.  Its rank is at most 3K=L.  Join E_ij to E_ijl
  through G(p_i join p_j), and make the analogous three choices.  Join
  E_i to E_ijl through G(p_i).
* Each small barycentric triangle with original vertex i now has its
  entire boundary in G(p_i).  Fill it in G(p_i), which is simply
  connected.  The paths from an edge midpoint to either adjacent face
  barycentre were chosen in the Grassmannian containing the pair join,
  so the two labelled subtriangles have exactly the same value on their
  common edge.

This gives one continuous e on the whole sphere.  More importantly, every
point x lies in a small triangle labelled by an original vertex i of the
same fine simplex, and e_x contains p_i.  Equations (C1)--(C2) therefore
give the soft carrier estimate

    ||A_x(q-e_x)||
      <=||A_x-A_i||+||A_i(q-p_i)|| < 3kappa/4<kappa.   (C3)

This is not a selection from a union of hard-carrier branches.  Only
finitely many fixed vertex carriers are used; their exact joins occur on
the appropriate lower-dimensional barycentric faces, and each 2-cell is
filled inside one ordinary Grassmannian.  Hence the known lower
semicontinuity failure for raw hard-carrier unions is not invoked.

If K=0, (C2) says every vertex has ||A_i||<=kappa/2, and (C1) gives
||A_x||<3kappa/4 everywhere.  The direct rotation contracts v to q and no
carrier is needed.

## 3. The small-source alternative and direct rotation

The complex Stiefel manifold

    St_n(q) ~= V_k(C^n)=U(n)/U(n-k)

is 2-connected when n-k>=1.  Indeed the block inclusion
U(n-k)->U(n) is an isomorphism on pi_1, while both unitary groups have
pi_2=0; the homotopy exact sequence gives pi_1=pi_2=0.

If K>0 and k<=3K, choose any filling, which exists by this computation.
Every point u of the filling obeys

    ||u-q||_2 <=2sqrt(k/n)
              <=4sqrt(3) delta/kappa.                  (C4)

It remains to treat k>=3K+1.  Let e be the carrier from Step 2, put
f=q-e, x_z=v(z)f_z, and y_z=f_z.  These partial isometries have common
initial projection f_z, and (C3) says ||x_z-y_z||<kappa.  The continuous
direct rotation supplies unitaries U_z with

    U_z x_z=y_z,       ||U_z-1||<=10kappa.

Its principal-log path gives a homotopy inside St_n(q), staying within

    delta+10kappa                                             (C5)

of q, from v to

    v'(z)=q-e_z+w_z,
    w_z^*w_z=e_z,       w_zw_z^* orthogonal to q-e_z.   (C6)

## 4. The localized pi_2 class is exactly c_1

Let c=n-k>=1.  For 0<=r<=k define Z_r to consist of pairs (E,W) with

    E<=q, rank(E)=r,
    W^*W=E,       WW^* orthogonal to q-E.

Projection to E makes Z_r a locally trivial bundle over
Gr_r(C^k).  Its fibre is

    V_r(C^(r+c))=U(r+c)/U(c).

Because c>=1, the exact sequence for U(c)->U(r+c) shows that this fibre
has pi_1=pi_2=0.  The base is simply connected.  Therefore

    pi_2(Z_r) -> pi_2(Gr_r(C^k))                         (C7)

is an isomorphism.  For 0<r<k the group on the right is Z, and the complete
invariant of a sphere E:S^2->Gr_r(C^k) is the first Chern class of its
tautological pullback.  When r=0 or r=k the base is a point and the same
conclusion is read as zero obstruction.

Apply this to the sphere (e,w) in Z_L from (C6).  The complement q-e is a
complex vector bundle of rank k-L>=1 over S^2 and

    c_1(q-e)=-c_1(e).                                   (C8)

Every rank-r complex bundle over S^2 is classified by its clutching class
in pi_1(U(r))=Z and is isomorphic to its determinant line plus r-1 trivial
lines.  Consequently q-e contains a line subbundle d satisfying

    c_1(d)=-c_1(e).                                     (C9)

Regard d also as its continuous rank-one projection.  Promote the localized
data by

    e'=e+d,       w'=w+d.                               (C10)

The ranges are orthogonal, so (e',w') lies in Z_(L+1).  Promotion does not
change the represented Stiefel point:

    q-e'+w'=q-e-d+w+d=q-e+w.                            (C11)

Moreover c_1(e')=0.  By (C7), the promoted sphere is null-homotopic in
Z_(L+1).  This includes the edge case L+1=k, where its Grassmannian base is
already a point.  A null-homotopy (E_y,W_y) gives the required filling of
v' by q-E_y+W_y.  Every point in this uncontrolled topological filling is
nevertheless metrically controlled, because its defect has right support
E_y:

    ||q-E_y+W_y-q||_2
      <=2sqrt((L+1)/n)
      <=8 delta/kappa.                                 (C12)

For the last inequality, K>=1 and hence

    L+1=3K+1<=4K<=16n delta^2/kappa^2.

Thus a single Chern-cancelling line kills the only degree-two obstruction;
no complement trace bound is used.  In particular k-L=1 is allowed.

## 5. The projection modulus

Put epsilon_0=min(epsilon,1) and choose

    kappa=epsilon_0/40,
    delta=epsilon_0^2/2560.                             (C13)

Then kappa<1/20.  The small-source bound (C4) is less than epsilon, the
localized bound (C12) equals at most epsilon_0/8, and (C5) is less than
epsilon.  Glue the direct-rotation homotopy on an outer collar of B^3 to
the localized null-homotopy on the inner ball.  This proves the quadratic
projection modulus for a sphere centred at q, and Step 1 transfers it to
every centre.

## 6. Replication and positive weights

For a projection weight p and a fixed base m-frame s_1,...,s_m, put

    Q=sum_j s_js_j^*.

The exact identification

    (t_j) |-> V=sum_j t_js_j^*

maps the projection-copy fibre isometrically onto St_n(Q), because

    ||V-V'||_2^2=sum_j||t_j-t'_j||_2^2.                (C14)

Strict slack makes Q proper, even if rank(1-Q)=1.

Now let a be an arbitrary positive contraction, p=supp(a), and let a
sphere in F_(n,m)(a) lie delta_w-close to a base tuple.  Write its unique
polar frames as v_j=s_ja^(1/2).  Set

    eta=(epsilon_0/12)^2,
    p_h=1_[eta,1](a),       p_l=p-p_h.

The high polar sphere satisfies

    (sum_j||s_jp_h-s_(0,j)p_h||_2^2)^(1/2)
      <=eta^(-1/2) delta_w.                             (C15)

Apply the projection theorem, through (C14), with output radius
epsilon_0/3.  It applies because the total high range is proper.  The
needed input is

    delta_w <=sqrt(eta) rho_(2,St)(epsilon_0/3)
             =epsilon_0^3/276480.                      (C16)

This fills the high polar frame over B^3.  Its moving range complement is
a complex vector bundle over the contractible ball and hence is trivial.
On the boundary, the low polar tuple is a map into

    V_(m rank(p_l))(C^(n-m rank(p_h))).

The unused target dimension is n-m rank(p)>=1, so this Stiefel manifold has
pi_2=0.  The boundary low frame therefore extends inside the moving
complement.  Combining the high and low frames and multiplying on the
right by a^(1/2) gives an exact weighted filling.

The high weighted displacement is at most epsilon_0/3.  Irrespective of
the chosen low extension,

    sum_j||(T_j-s_(0,j))a^(1/2)p_l||_2^2
       <=4m tau(ap_l)
       <=4eta m tau(p_l)
       <=4eta,                                          (C17)

so the low cost is at most epsilon_0/6.  Equations (C16)--(C17) prove the
cubic modulus in the claim.

Finally, in finite dimension multiplication by a^(1/2) is a homeomorphism
from the polar-frame fibre on p onto the weighted fibre; the inverse uses
the bounded inverse of a^(1/2) on p.  By (C14) the polar-frame fibre is
V_(m rank(p))(C^n), whose complement has positive dimension.  It is
2-connected by Step 3.  This proves global 2-connectivity.  Combining the
new degree-two estimate with the required degree-one theorem and the
standard direct-rotation path estimate gives the asserted uniform
equi-LC^2 statement.
