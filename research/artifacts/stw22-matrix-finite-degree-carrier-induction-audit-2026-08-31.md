# Audit: all finite-degree matrix carrier and Bott induction

## Verdict

For every fixed j>=2, every normalized matrix factor, and every
weighted-copy fibre with unused rank c satisfying 2c>=j, the proof gives

    rho_(j,St)(epsilon)
      =min(epsilon,1)^2/(2560 C_j),

    rho_j(epsilon)
      =min(epsilon,1)^3/(276480 C_j),

where

    C_j=j+1+t(t+1)/2+floor(j/2),
    t=floor((j-1)/2).

The constants are uniform in matrix size, ranks, weight, copy number, and
the positive amount of slack.  Every such fibre is globally
j-connected.  The modulus is degreewise; no uniformity as j tends to
infinity is claimed.

## Defect and carrier checks

The spectral cutoff has rank at most

    K=floor(4n delta^2/kappa^2).

Finite-dimensional norm equivalence and a sufficiently fine
triangulation give operator-norm variation below kappa/2 on every
simplex.  The initial barycentric two-skeleton carrier has rank
(j+1)K, contains a hard carrier from a nearby original vertex at every
point, and therefore preserves the operator-norm tail bound below
kappa.  The K=0 branch is consequently direct-rotation small.

For a d-cell, its least face has dimension at most j-d.  The containing
Grassmannian therefore has variable tautological rank at least dK.  At
stage h, the complement rank is at least h+1.  These are exactly the
finite stable-range inequalities used to extend the carrier, and all
extensions occur inside the least-face containing Grassmannian.

Over a 2h-complex, a rank-s complement with s>=h splits as a rank-h
bundle plus a trivial rank-(s-h) bundle.  Promoting the rank-h block
leaves the new complement trivial.  The promoted carrier is stably
trivial and, because its rank exceeds h, actually trivial.  This kills
the even boundary obstruction.  Odd Grassmannian homotopy vanishes in
the same two-sided stable range.  Iteration h=1,...,floor((j-1)/2)
produces a global carrier of rank

    (j+1)K+t(t+1)/2.

## Localized obstruction check

The localized pair space fibres over the carrier Grassmannian with fibre

    V_R(C^(R+c)).

That fibre is 2c-connected, so its pi_(j-1) and pi_j vanish under
2c>=j.  Localized pi_j is therefore exactly the Grassmannian pi_j.

In odd degree j=2r+1, both Grassmannian blocks have rank at least r+1.
The stable odd unitary addition map is surjective and the adjacent even
groups vanish, so pi_j of the base is zero.

In even degree j=2r, split the carrier complement over S^(2r) as a
rank-r block D_r plus a trivial bundle, and promote D_r into both the
carrier and partial isometry.  This leaves the represented Stiefel point
exactly unchanged.  Crucially, nullity is not inferred merely from an
even unitary group.  The remaining complement bundle is trivial, the
promoted carrier rank R' is greater than r, and

    Gr_(R')(C^(R'+s-r)) -> BU(s-r)

is 2R'-connected.  Thus the trivial complementary class is the complete
obstruction and the finite-Grassmannian sphere is null.  This explicitly
excludes unstable torsion and CP^1 phenomena.

## Constants, weights, and sharpness

The small-source branch and every localized filling cost at most

    4sqrt(C_j) delta/kappa.

The final carrier rank is at most C_j K.  Taking
kappa=epsilon_0/40 and
delta=epsilon_0^2/(2560 C_j) leaves room for the direct-rotation collar.
The standard high-low split with eta=(epsilon_0/12)^2 gives the cubic
weighted modulus.  The low boundary Stiefel group pi_j vanishes in the
same codimension range.

For sharpness, the explicit sphere varies the first vector in

    span{e_1,e_(n-c+1),...,e_n}

and fixes the remaining frame vectors.  The forget-first-vector
fibration identifies it with a generator of pi_(2c+1)=Z, while its
normalized radius is at most 2/sqrt(n).  Hence the codimension condition
is both the global-connectivity threshold and the sharp uniform local
threshold across shrinking positive slack.

An independent hostile audit checked the skeleton indexing, bundle
splitting, containing-Grassmannian stable ranges, even-degree
finite-Grassmannian classification, localized fibration, rank constants,
weighted transfer, trace corollary, and explicit generator.  It
green-lit the result after the complement-classification argument above
was made explicit.
