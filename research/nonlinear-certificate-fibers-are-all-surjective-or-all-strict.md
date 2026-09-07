---
rg: 2
id: nonlinear-certificate-fibers-are-all-surjective-or-all-strict
kind: claim
artifacts:
  - research/artifacts/lamp-and-nonlinear-fiber-literature-audit-2026-09-07.md
title: An injective nonlinear automaton with unchanged full-shift certificates is either surjective on every fiber or strict on every fiber
distinct_from:
  one-invertible-certificate-fiber-forces-global-invertibility: that uses finite-rank linear perturbations and gives group-algebra consequences; this uses finite-alphabet counting and needs neither linearity nor a local decoder.
---

Let G be any group and let A and B be finite nonempty alphabets. Suppose
a cellular automaton on the entire product full shift has the form

    E(x,c)=(T_c(x),c),       x in A^G, c in B^G,

and E is injective. The maps T_c may be arbitrary nonlinear local maps
in their data, with a uniform finite dependence on data and certificates.
Then exactly one of the following holds:

1. Every T_c is bijective, and E is surjective.
2. Every T_c is injective and nonsurjective, and E is nonsurjective.

In particular, surjectivity of ONE certificate fiber forces surjectivity
of every fiber. The initial certificate need not be constant or periodic.

For each b in B let c_b(g)=b for every g. If E is injective and
nonsurjective, the map T_(c_b) is an ordinary injective nonsurjective
cellular automaton on A^G for EVERY b. Thus the strict behavior already
occurs over the same group and the original data alphabet at every
constant certificate; it cannot occur only on certified computations.

The same dichotomy holds when the certificate evolves independently of
the data by a reversible cellular automaton chi:

    E(x,c)=(T_c(x),chi(c)).

Compose the output certificate with chi^(-1) to recover the preceding
case. More generally, if chi is only assumed surjective, E is injective,
and one T_c is surjective, then E is bijective and chi is necessarily
bijective. Thus a reversible autonomous certificate update does not
remove the obstruction.

The elementary mechanism is finite-output rigidity: an injective map
of A^G which differs from a bijection only in finitely many output
coordinates is itself bijective. Finite changes of a certificate cause
only finitely many output coordinates of its local data rule to change.
These certificates are dense, and compactness of A^G makes fiberwise
surjectivity a closed condition.

Consequently a certificate-preserving self-verifying construction cannot
combine global injectivity, one reversible certificate background, and
strictness elsewhere, even with nonlinear data processing. This is not
a proof of Gottschalk's conjecture: strict ordinary cellular automata on
the constant fibers have not been excluded. It gives no decision algorithm
for surjectivity of a specified nonconstant fiber. It also does not cover
data-dependent certificate updates or restriction to a proper certificate
subshift whose finite-modification classes need not be dense.
