# Audit: dimension-free matrix two-sphere fillings

## Result and scope

For every normalized matrix factor, every replication number, and every
positive weight with one unused target dimension, two-spheres in a
sufficiently small Hilbert-sum 2-ball fill in a prescribed larger ball.
The explicit modulus is

    min(epsilon,1)^3/276480.

For projection weights the modulus is quadratic,

    min(epsilon,1)^2/2560.

There is no dependence on matrix size, ranks, replication number, weight,
or the numerical size of the positive slack.  This is a matrix theorem; it
does not assert a factor-uniform degree-two modulus for diffuse factors.

## Carrier audit

The only use of finite-dimensional norm equivalence is to refine the
triangulation of the given sphere until A_x is operator-norm close to the
three vertex values of each face.  The number of triangles is unrestricted
and never enters the modulus.

Each vertex carrier has rank at most

    K=floor(4n delta^2/kappa^2).

On the barycentric subdivision, a vertex, edge midpoint, and face
barycentre use respectively one-, two-, and three-carrier joins.  Thus the
global carrier has rank L=3K.  Every small triangle is filled in the simply
connected Grassmannian of L-planes containing its labelled vertex carrier.
The edge-midpoint-to-face-barycentre path lies in the Grassmannian
containing the pair join, so adjacent labelled triangles agree on their
common edge.  Every point therefore contains at least one carrier from a
nearby original vertex and the residual operator norm is below kappa.

This construction does not select from the non-lower-semicontinuous union
of hard carrier branches.  The carriers are fixed after the triangulation,
joins are used only on the appropriate skeleton, and ordinary
Grassmannian connectivity performs the interpolation.

If K=0, the whole sphere is operator-norm small and direct rotation
contracts it.  If rank(q)<=3K, ordinary 2-connectivity gives an arbitrary
filling, but the normalized 2-diameter of the entire Stiefel manifold is
at most 4sqrt(3)delta/kappa.  These branches remove every additive-rank
loss.

## Topology audit

For c=n-rank(q)>=1, the localized configuration Z_L has base
Gr_L(C^rank(q)) and fibre V_L(C^(L+c)).  The fibre has pi_1=pi_2=0, hence
pi_2(Z_L) is identified with pi_2 of the Grassmannian.  The complete
obstruction of a sphere is c_1 of its moving carrier bundle.

The complement q-e has positive rank and first Chern class -c_1(e).
Complex bundles over S^2 split as their determinant line plus a trivial
bundle, so q-e contains a line d with c_1(d)=-c_1(e).  Replacing

    (e,w) by (e+d,w+d)

kills the obstruction while leaving the represented frame exactly
unchanged.  This remains valid when q-e has rank one and when e+d=q.
Every point of the resulting filling is supported on rank L+1, giving

    2sqrt((L+1)/n) <= 8delta/kappa.

The ambient complement c may also have rank one; c>=1 is exactly what makes
the Stiefel fibre have vanishing pi_1 and pi_2.

## Weighted and global checks

Replication is an exact isometry to one Stiefel space in the Hilbert-sum
metric.  The high spectral frame uses the quadratic projection modulus.
The low frame extends over B^3 because its residual complex Stiefel fibre
has positive complement and vanishing pi_2.  Its weighted cost is at most
2sqrt(eta), independent of its unweighted motion.

For a fixed matrix weight, polar decomposition is a homeomorphism between
the weighted fibre and a complex Stiefel manifold with positive complement.
Thus every fibre is globally 2-connected, not merely locally fillable.

An independent hostile audit checked the carrier gluing, the two homotopy
exact sequences, the Chern-line promotion, the rank-one edge cases, and
the normalized-rank constants; it found no unresolved gap.
