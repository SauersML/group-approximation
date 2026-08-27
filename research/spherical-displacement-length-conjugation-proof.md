---
rg: 2
id: spherical-displacement-length-conjugation-proof
kind: route
title: Pair the cloud twice and push the isometry through the shadow
target: spherical-displacement-length-is-not-conjugation-invariant
requires:
  - spherical-tight-single-colour-near-perfect-matching
---

**Length axioms.**  Immediate from the triangle inequality in `R^d`,
Minkowski's inequality in `L^r` of the uniform counting measure on `[N]`, and
the fact that a permutation is measure preserving.  Symmetry follows by the
substitution `j |-> c^(-1)(j)`.

**Failure of conjugation invariance.**  Two near-perfect pairings of the cloud
are needed.  The first is a greedy nearest-neighbour pairing: for an iid
uniform cloud the nearest-neighbour distance of all but `o(N)` points tends to
zero as `N->infinity` at fixed `d`, and removing matched pairs one at a time
leaves the remaining points still uniform enough to continue, so all but
`o(N)` indices are paired within `eta(N)->0`.  The second is the tight
matching of the cloud against its own antipodal image, which is the case
`U=-I` of `spherical-tight-single-colour-near-perfect-matching`; it pairs all
but `o(N)` indices with a point within `eta(N)` of their antipode.

Let `c` be the involution swapping the first pairing's pairs and fixing the
rest, and let `h` be any bijection of `[N]` carrying each near pair onto a
distinct antipodal pair (both families have `(1/2-o(1))N` pairs, so such an
`h` exists after discarding `o(N)` indices).  Then `hch^(-1)` swaps antipodal
pairs, so it moves `(1-o(1))N` points by `2-o(1)`, giving `(SDL3)`.  Since the
inflation reaches the diameter, no rescaling of the length repairs the
hypothesis.

**Shadow invariance.**  Substituting `j=sigma(i)` is legitimate because
`sigma` is a bijection and the measure is uniform.  Inequality `(SDL6)` is
three applications of the triangle inequality together with `||Uv-Uw||=||v-w||`.
Taking `L^r` norms, the good set contributes `ell_r(c)+2 rho`; the bad set has
density at most `2 theta` (it is contained in `E union c^(-1)E`, and `c` is
measure preserving) and each of its terms is at most the diameter `2`.  This
gives `(SDL5)`, and exchanging the roles of `c` and `sigma c sigma^(-1)`
— using that `sigma^(-1)` shadows `U^(-1)` at the same radius off `sigma(E)`
— gives the other direction.
