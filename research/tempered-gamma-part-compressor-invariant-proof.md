---
rg: 2
id: tempered-gamma-part-compressor-invariant-proof
kind: route
title: Same equal-trace transport as for the finite-dimensional part; weak containment restricts along subgroups and passes to the reduced C*-algebra
target: tempered-gamma-part-of-a-model-is-compressor-invariant
requires:
  - finite-dimensional-gamma-part-of-a-model-is-compression-blind
---

Write `u = pi(t)`, `Gamma' = t^(-1) Gamma t >= Gamma`, and for a subgroup
`Lambda` let `T_Lambda` be the closure of the sum of all closed
`L_Lambda`-invariant subspaces of `H = L^2(N)` on which the `Lambda`-action is
weakly contained in `lambda_Lambda`.  Weak containment in the regular
representation is preserved by subrepresentations and by direct sums, so
`T_Lambda` is itself an `L_Lambda`-invariant subspace whose representation is
weakly contained in `lambda_Lambda` (a direct sum of tempered representations
is tempered).

**(1) Module, centralizer, transport.**  For a tempered closed invariant
subspace `F` and a unitary `x in U(N)`, right multiplication `F |-> F x` is a
unitary equivalence of `Lambda`-representations commuting with `L_Lambda`, so
`F x` is tempered; right multiplication by general `x in N` is a linear
combination of unitaries, so `T_Lambda` is a closed right `N`-submodule and
`e_(T_Lambda)` is left multiplication by a projection `f in N`.  Invariance
under `L_Lambda` and under left multiplication by `pi(Lambda)' cap N` is as in
`fd-gamma-part-compression-blind-proof`.  Monotonicity: the restriction of
`lambda_(Gamma')` to `Gamma` is a multiple of `lambda_Gamma`, so a
`Gamma'`-subrepresentation weakly contained in `lambda_(Gamma')` restricts to
a `Gamma`-representation weakly contained in `lambda_Gamma`; hence
`T_(Gamma') <= T_Gamma`.  The unitary `V xi = u^* xi u` intertwines `L_Gamma`
with `L_(Gamma') o Ad(t^(-1))` and carries `lambda_Gamma` to
`lambda_(Gamma')` under the isomorphism `Ad(t^(-1)) : Gamma -> Gamma'`, so
`V T_Gamma = T_(Gamma') <= T_Gamma`; as elements of `N`, `u^* f u <= f` with
equal trace, so `u^* f u = f` and `T_(Gamma') = T_Gamma`.

**(2) Orthogonality to the finite-dimensional part.**  If a
finite-dimensional representation `sigma` of `Gamma` were weakly contained in
`lambda_Gamma`, then `sigma (x) bar sigma`, which contains the trivial
representation, would be weakly contained in `lambda_Gamma (x) bar sigma`, a
multiple of `lambda_Gamma`, forcing `Gamma` amenable (Hulanicki--Reiter).  So
for non-amenable `Gamma` no finite-dimensional subrepresentation lies inside
`T_Gamma`.  The projection `e f` is `L_Gamma`-invariant and its range lies in
`T_Gamma`, so its `Gamma`-representation is tempered; it also lies in the
closure of the finite-dimensional subrepresentations, so if nonzero it would
contain a nonzero finite-dimensional subrepresentation (the closure of a sum
of finite-dimensional invariant subspaces is a direct sum of
finite-dimensional invariant subspaces, and a nonzero invariant subspace of
such a direct sum contains a finite-dimensional one).  Hence `e f = 0`.

**(3) A trace of the reduced algebra.**  Since `f` commutes with
`pi(Gamma)`, `chi_f(gamma) = tau(pi(gamma) f)/tau(f)` is a normalized
positive-definite function on `Gamma` and it is tracial:
`tau(pi(gamma gamma') f) = tau(pi(gamma) f pi(gamma')) = tau(pi(gamma') pi(gamma) f)`.
It is the diagonal coefficient of the vector `f / ||f||_2 in T_Gamma` in the
`Gamma`-representation `L_Gamma|_(T_Gamma)`, which is weakly contained in
`lambda_Gamma`; coefficients of representations weakly contained in
`lambda_Gamma` extend to states of `C*_r(Gamma)`.  A tracial positive-definite
function that extends to `C*_r(Gamma)` is a tracial state of `C*_r(Gamma)`.

**(4) Support on the amenable radical.**  Breuillard--Kalantar--Kennedy--
Ozawa prove that every tracial state of `C*_r(Gamma)` is supported on the
amenable radical of `Gamma`.  If that radical is a finite central subgroup
`Z`, then `chi_f(gamma) = 0` for `gamma notin Z`, so the GNS algebra of
`chi_f`, which is `pi(Gamma)'' f` with the trace `tau(. f)/tau(f)`, is the
group von Neumann algebra of `Gamma` with the character
`gamma |-> chi_f(gamma)` on `Z`, i.e. the corner `L(Gamma) z_chi` where
`z_chi in L(Z)` is the central projection of the character `chi_f|_Z`.

**The Kun--Thom subgroup.**  The sandwich theorem (Vaserstein) shows a
non-central normal subgroup of `EL_r(R_+)`, `r >= 3`, contains `E_r(R_+, I)`
for a nonzero ideal `I`.  Pick `a, b in I` of positive `x_1`-degree with
nonzero leading coefficients after specializing `x_2, ..., x_d` to elements of
`F_q` (possible since `I` is a nonzero ideal of a polynomial ring), and view
`e_12(a), e_21(b)` inside `SL_2(F_q((x_1^(-1))))` acting on its Bruhat--Tits
tree.  The product `e_12(a) e_21(b)` has trace `2 + ab` of absolute value
`q^(deg ab) > 1`, so it is hyperbolic; `e_12(a)` fixes the end `infinity`
and `e_21(b)` fixes the end `0`, neither fixes the other's end, and no point
is fixed by both a hyperbolic element and the group, so the group they
generate is a non-elementary group of tree automorphisms and contains a free
subgroup (ping-pong).  Hence every non-central normal subgroup is
non-amenable, the amenable radical is the center `Z = mu(F_q) cap EL_r`,
finite, and (4) applies.
