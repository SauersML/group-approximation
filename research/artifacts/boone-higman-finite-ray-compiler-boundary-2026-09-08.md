# The finite-ray compiler stops at virtually cyclic inputs

The cyclic zigzag construction does not extend to Z^2 by using more
periodic rays. The exact boundary is now proved: an infinite input P
admits a realization E_nu(P)<=E_m for some enumeration and finite m
if and only if P is virtually cyclic. The same restriction holds after
conjugating the entire permutation action by any relabeling.

## Why the regular action matters

Pass from a subgroup of E_m to the finite-index subgroup that fixes all
ray germs. Each ray then gives an integer translation homomorphism.
If the original subgroup has an infinite free orbit, some ray meets that
orbit infinitely often. A zero translation on that ray fixes one of
those points, so freeness makes the element trivial. The corresponding
translation homomorphism is injective, giving an infinite cyclic
subgroup of finite index.

The original copy of P in E_nu(P) acts regularly on the even positions,
so this argument always applies. It is not enough that a finite-ray
group can contain P through some different action. For example,
Houghton groups contain higher-rank abelian subgroups, but those
subgroups cannot have the free orbit required by this construction.

Conversely, choose an infinite cyclic normal subgroup <t> of finite
index d in a virtually cyclic P. On coordinates t^k r_i, left
multiplication acts by signed affine maps k->epsilon*k+c_i, with a
permutation of the d cosets. Splitting each line into its positive and
negative rays gives an explicit enumeration whose regular permutations
are eventually 2d-periodic. Moving them to the even numbers and adjoining
E_2 gives containment in E_(4d).

The full proof is `finite-ray-regular-orbit-classification-proof`.
The converse is a containment statement. It does not prove finite
presentation of every exact E_nu(P) subgroup. For Z, the separate
index-twelve calculation is what supplied finite presentation.

## A broader bounded-displacement attempt also fails for Z^2

For an injective enumeration nu and finite symmetric generating set S,
let D_nu(r) be the largest generator jump from a point in the radius
r-1 word ball. Following words of length at most r gives

    |B_r| <= 2r*D_nu(r)+1.

For Z^2, |B_r|=1+2r(r+1), hence D_nu(r)>=r+1. Thus permitting
nonperiodic generators while keeping their displacement uniformly
bounded still cannot accommodate the regular input. This does not
exclude other embeddings of Z^2 in bounded-displacement permutation
groups; it is an obstruction to the regular enumeration itself.

## A two-dimensional repair that does not yet provide a host

One could transport the slide along the standard outward square spiral
on Z^2. This moves the original translations back into their natural
two-dimensional setting, but the slide then needs different pieces.
In the positive quadrant the spiral successor moves north when x>y
and west when y>=x. Both regions meet every positive quadrant tail.

In the cubical setting, Bieri-Sach define their piecewise isometric and
piecewise translation groups using finite partitions into axis-aligned
orthants; see [Section 3.3](https://doi.org/10.1112/jlms.12503).
A finite such partition of the positive quadrant has a piece containing
a positive quadrant tail. The spiral successor cannot agree with one
translation there, because it has the two directions just described.
Nor can a nontranslation Euclidean isometry agree with it on that tail:
the successor has bounded displacement, whereas a nonidentity linear
part has unbounded displacement on a full quadrant tail.

Therefore this particular slide is not a cubical piecewise isometry.
It cannot be put under that finiteness theorem just by recognizing the
other generators as ordinary lattice translations. This does not rule
out a different enumeration, a different tessellation or a suitable
group with more general pieces. No finitely presented Z^2 shift envelope
has been obtained from this attempt.

## Integration and verification scope

The finite-ray classification and growth bound are new established
claims in the Boone-Higman part of Cairn, with complete prose proofs.
They constrain `infinite-shift-higman-compiler` and delimit the positive
cyclic prototype. The universal compiler and the main conjecture remain
open. These claims are not Lean-verified; the automated workflow checks
their graph integration. No GPU ran or Civo instance was provisioned.
