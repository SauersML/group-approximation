# Audit: matrix LC4 via Bott cancellation

## Result

For every normalized matrix factor and every weighted-copy fibre with at
least two unused target dimensions, four-spheres have the projection
modulus

    min(epsilon,1)^2/2560

and the weighted modulus

    min(epsilon,1)^3/276480.

Every such fibre is globally 4-connected.  The constants are independent
of matrix size, ranks, weights, and copy number.

## Carrier skeleton

The barycentric carrier uses joins from at most five original vertices,
so its initial rank is 5K.  It is built first on the two-skeleton.  A
single determinant line in its complement cancels c_1 globally there.
This makes every three-cell boundary null in its containing Grassmannian.
The resulting rank-(5K+1) carrier then extends over each four-cell because
the relevant containing Grassmannian has variable rank 4K+1>=5 and
vanishing pi_3.  This excludes the CP^1 exception explicitly.

At every skeleton and cell stage the extension is made inside a
Grassmannian containing a carrier from a vertex of the same fine original
four-simplex.  Thus operator-norm tail control is never lost.

## Localized Bott class

For codimension c>=2, the fibre V_R(C^(R+c)) of the localized
configuration has pi_3=pi_4=0, including c=2.  Hence localized pi_4 is
exactly the pi_4 class of the moving carrier in its complex Grassmannian.

If the carrier complement has rank zero or one, this base pi_4 is zero.
If it has rank at least two, its bundle over S^4 splits as a rank-two
bundle D plus a trivial bundle.  The rank-two piece carries the complete
clutching, equivalently c_2, class.  Promoting both carrier and localized
partial isometry by D leaves the represented frame exactly unchanged and
makes c_2 of the promoted carrier zero.  The new base sphere, and hence
the localized sphere, is null.

The unstable fact pi_4(U(2))=Z/2 introduces no extra obstruction.  The
block map on pi_3 is an isomorphism, so the c=2 Stiefel fibre still has
vanishing pi_3 and pi_4.

## Constants and scope

The small-source branch costs less than 9delta/kappa.  The final carrier
has rank at most

    5K+3<=8K<=32n delta^2/kappa^2,

so the localized branch costs less than 12delta/kappa.  The choices
kappa=epsilon_0/40 and delta=epsilon_0^2/2560 leave ample room.

High-low transfer over B^5 preserves the two-dimensional unused target
corner, and the low Stiefel fibre has pi_4=0.  This gives the same cubic
weighted modulus as in degrees two and three.

The theorem is scoped to complement rank at least two.  Codimension one
already fails global 3-connectivity, although this audit makes no claim
about the nullity of each individual S^4 map.  Half slack with replication
m>=2 automatically lies in the positive range for every nonzero matrix
fibre.

An independent hostile audit checked the barycentric gluing, determinant
line, pi_3 of all containing Grassmannians, finite-Grassmann pi_4 cases,
rank-two bundle splitting over S^4, the unstable U(2) torsion, localized
homotopy sequence, constants, weighted transfer, and scope.  It found no
unresolved gap.
