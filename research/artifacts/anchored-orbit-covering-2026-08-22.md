# Anchored orbit covering for exact wreath packets

Hayes' definition fixes a microstate sequence `D_d` for one diffuse
self-adjoint and counts ordinary covers of the remaining coordinates.  This
is equivalent to orbital covering because the unitary centralizer of a
diffuse pin has zero `d^2`-normalized covering entropy.

The finite-level mechanism is explicit.  Cut the spectrum of `D_d` into `m`
asymptotically equal-rank blocks.  A commuting unitary is block diagonal, so
its net exponent is proportional to the sum of the squared block ranks,
which is at most `d^2/m+o(d^2)`.  Letting `m` grow kills the normalized
exponent.

Hence intersecting a single global representation orbit with `pin=D_d`
produces only a centralizer orbit and still has zero quadratic entropy.  A
union of `exp(o(d^2))` representation classes remains entropy-null.  This
puts the exact finite congruence-wreath no-go directly into the anchored
microstate language and eliminates the apparent possibility that fixing the
diffuse lamp observable resurrects the large homogeneous-space torsor.
