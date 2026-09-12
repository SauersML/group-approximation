# Audit: matrix LC3 and the codimension barrier

## Exact verdict

The matrix degree-three problem has a sharp integer-codimension split.

* With at least two unused target dimensions, projection Stiefel fibres
  have the quadratic sphere modulus min(epsilon,1)^2/2560, and arbitrary
  positive weighted-copy fibres have the cubic modulus
  min(epsilon,1)^3/276480.  The moduli are independent of all matrix
  sizes, ranks, copy numbers, and weights.
* With exactly one unused target dimension and nonzero source,
  pi_3 is Z.  Essential SU(2) spheres have normalized radius at most
  sqrt(8/n), so no modulus is uniform as matrix size grows and positive
  slack is allowed to shrink.

The negative statement concerns the full merely-positive-slack fibre
family and the associated uniform Michael/Stiefel mechanism.  It does not
rule out every possible dimension-four trace theorem by unrelated methods,
and it is not phrased as failure for each fixed gamma.

## Barycentric carrier check

At an original simplex sigma, the fixed projection P_sigma is the join of
the carriers at its vertices, so its rank is at most 4K.  A barycentric
edge sigma<tau is interpolated in the Grassmannian containing P_sigma.
For a barycentric triangle sigma_0<sigma_1<sigma_2, every boundary edge
lies in the Grassmannian containing P_(sigma_0), which is simply connected.
Consequently all face fillings glue on the two-skeleton and retain at least
one carrier from a nearby original vertex.

The construction does not select from a moving union of hard-carrier
branches.  The triangulation is chosen after fixing n, fixed joins occur
on its skeleton, and only their rank--not the mesh size or number of
simplices--enters the estimate.

## Determinant-line check

The complement q-e over the finite two-dimensional skeleton has positive
rank.  Complex vector bundles over a two-dimensional CW complex are
classified by c_1 and split as their determinant line plus a trivial
bundle.  Hence q-e contains a genuine line subbundle d with
c_1(d)=-c_1(e).  Promotion to E=e+d is made once over the whole skeleton,
not separately on each tetrahedron.

The promoted bundle has c_1(E)=0.  Each top barycentric cell has a
distinguished original vertex i, and every point of its boundary contains
p_i.  The boundary therefore maps to the Grassmannian of rank-R planes
containing p_i.  Its pi_2 class is detected by the tautological c_1, so it
fills inside that same Grassmannian.  The carrier estimate survives in
the cell interior.

## Localized topology and constants

The localized configuration has fibre V_R(C^(R+c)).  For c>=2 its pi_3
vanishes.  Its Grassmannian base has pi_3=0 in the carrier range
R=4K+1>=5; the exceptional CP^1 case cannot occur.  Thus pi_3 of the
configuration vanishes.

The small-source branch costs at most 8delta/kappa.  In the carrier branch,

    R<=5K<=20n delta^2/kappa^2,

so every point of an arbitrary localized filling costs less than
9delta/kappa.  With kappa=epsilon_0/40 and
delta=epsilon_0^2/2560, these bounds and the direct-rotation collar all
lie safely inside epsilon.

The high-low transfer over B^4 preserves two unused dimensions both in
the high projection frame and in the residual low Stiefel fibre.  The
weighted input radius is exactly epsilon_0^3/276480.

## Obstruction and trace relevance

The quotient U(n)->U(n)/U(1) is an isomorphism on pi_3.  A standard SU(2)
block is a generator, while its normalized Hilbert-Schmidt displacement
is at most sqrt(8/n).  This verifies both essentiality and metric collapse.

For half slack and m>=2, every nonzero matrix source has total rank between
2 and n/2; its complement therefore has rank at least two.  The obstruction
is absent in precisely the replication range needed by the trace-gap
argument.  A dimension-four all-factor theorem would still require the
diffuse degree-three analogue and the corresponding stabilized selection
step.

An independent hostile audit checked the polar-frame identification, the
barycentric gluing, determinant-line extraction, cellwise Chern
cancellation, the CP^1 exception, localized homotopy sequence, all rank
edge cases, metric constants, weighted transfer, and the scope of the
negative conclusion.  It found no unresolved gap.
