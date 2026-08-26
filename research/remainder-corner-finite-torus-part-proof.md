---
rg: 2
id: remainder-corner-finite-torus-part-proof
kind: route
title: Monotone potentials along the decomposition transport; valuations and Newton polytopes for finite-orbit subvarieties
target: remainder-corner-fiber-kernels-have-finite-torus-part
requires:
  - remainder-corner-fiber-kernels-are-monomial-free
  - kt-remainder-corner-characters-are-infinite-index-induced
---

**(1) Stationarity.**  In `remainder-corner-monomial-free-proof`, `mu = int
nu_omega dmu` with `nu_omega` the decomposition of `chi_omega o phi_A`; every
component `chi_(omega')` of `chi_omega o phi_A` satisfies `chi_(omega') = 1`
wherever `chi_omega o phi_A = 1`, in particular on `E(R_+, phi_A^(-1)(J_omega))`
(`phi_A` maps `E(R_+, phi_A^(-1) J)` into `E(R_+, J)`), so
`J_(omega') supseteq phi_A^(-1)(J_omega)`.  Drawing `omega ~ mu` and then
`omega' ~ nu_omega` gives a coupling of two copies of `mu`.  If `h(J') <= h(J)`
along `J' supseteq phi_A^(-1)(J)`, then `h(J_(omega')) <= h(J_omega)` with
equal laws; for bounded monotone `g`, `E g(h(J_(omega'))) = E g(h(J_omega))`
forces equality a.s.

**(2) Torus part.**  `V(phi_A^(-1) J) = closure(Phi_A(V(J)))` since
`(f o phi_A)(p) = f(Phi_A(p))`; on the torus `Phi_A` is an automorphism
(inverse `Phi_(A^(-1))`), so `V^0(phi_A^(-1) J) = Phi_A(V^0(J))` and
`V^0(J') subseteq Phi_A(V^0(J))` for `J' supseteq phi_A^(-1)(J)`.  Take
`h_1 = dim V^0` (monomial-freeness gives `V^0(J) != emptyset`: otherwise
`x_1...x_d` vanishes on `V(J)`, so a power of it lies in `J`).  By (1),
`dim V^0(J_(omega')) = dim Phi_A(V^0(J_omega))` a.s.; then each
top-dimensional component of `V^0(J')` lies in a top-dimensional component
of `Phi_A(V^0(J))`, so `h_2 = number of top-dimensional components` is
non-increasing and a.s. constant, forcing `T(J') = Phi_A(T(J))` (irreducible
closed sets of equal dimension nested are equal).  `T(J)` is a union of
components of an `F_q`-variety permuted by Galois, hence `F_q`-defined, so
`T` takes countably many values; `(Phi_A)_* law(T) = law(T)` with `Phi_A` a
bijection of that countable set gives invariance under `Phi_A^(-1)` as well;
transvections generate `SL_d(Z)`, so the law is `SL_d(Z)`-invariant, and an
invariant probability measure on a countable set charges only finite
orbits.

**(3) Finite-orbit subvarieties.**  Let `Lambda <= SL_d(Z)` of finite index
stabilize the irreducible `V` with `1 <= dim V <= d - 1`, and let
`I = I(V) subset bar F_q[x_1^(+-1), ..., x_d^(+-1)]`, a nonzero prime ideal
containing no monomial.  `Phi_A(V) = V` gives `phi_A^(-1)(I) = I`, so
`f in I` implies `f o phi_A in I` for `A in Lambda`.  Pick `0 != f in I` with
exponent support `S subset Z^d`, `|S| >= 2`, and let `K = bar F_q(V)`.  Since
`dim V >= 1` and the `x_i` are units of `K`, some discrete valuation `nu`
of `K` trivial on `bar F_q` has `theta := (nu(x_1), ..., nu(x_d)) != 0`
(otherwise every `x_i` would have neither zeros nor poles on a normal
projective model and be constant, making `V` a point).  In `K`,
`sum_(v in S) c_v x^(A v) = 0`, and the ultrametric inequality forces the
minimum of `<A v, theta> = <v, A^T theta>` over `S` to be attained at least
twice, for every `A in Lambda`.  The set of directions `theta'` for which
`min_(v in S) <v, theta'>` is attained at least twice is closed in
`R^d - 0` (its complement, unique minimizer, is open), and it contains the
orbit `Lambda^T theta`, which is dense in `P^(d-1)(R)` (the action of a
finite-index subgroup of `SL_d(Z)` on the projective space is minimal).
So every direction attains the minimum at least twice; but a vertex of the
Newton polytope `conv(S)` is exposed by some direction as the unique
minimizer.  Contradiction.

**(4) Conclusion.**  By (2) and (3) every top-dimensional component of
`V^0(J_omega)` is a point or the torus; the torus is excluded since
`J_omega != 0`; so `dim V^0(J_omega) = 0` and `V^0(J_omega)` is finite.  Then
`R/JR` is finite for `R = F_q[x^(+-1)]`, i.e. the saturation
`S = J : (x_1...x_d)^infty = JR cap R_+` is cofinite, and by Noetherianity
`(x_1...x_d)^M S subseteq J` for some `M`.  For the transport of `S`:
`phi_A^(-1)(J)^sat supseteq phi_A^(-1)(J^sat)` (if `x^u phi_A(h) in J` then
`x^(A w) phi_A(h) in J` for `w` with `A w >= u`), so
`S' supseteq phi_A^(-1)(S)`, and `colength(phi_A^(-1) S) <= colength(S)`
because `phi_A` induces an injection `R_+/phi_A^(-1)(S) -> R_+/S`.  The
potential `colength(S)` is non-increasing, hence a.s. constant, so
`S' = phi_A^(-1)(S)` and the injection is an isomorphism, i.e.
`phi_A(R_+) + S = R_+`.
