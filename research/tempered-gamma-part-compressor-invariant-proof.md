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
for a nonzero ideal `I`.  Pick a nonzero `c in I` and put `a = c x_1`, `a' = c x_1^2`, `b = c x_1`,
all in `I`.  Let `K = F_q(x_2, ..., x_d)((x_1^(-1)))`, a field complete for
the discrete valuation `-deg_(x_1)`, and view `e_12(a), e_12(a'), e_21(b)`
in `SL_2(K)` acting on the Bruhat--Tits tree of `SL_2(K)`, whose ends are
the points of `P^1(K)`.  An element of `SL_2(K)` is hyperbolic exactly when
its trace has absolute value `> 1`; `tr(e_12(a) e_21(b)) = 2 + ab` and
`tr(e_12(a') e_21(b)) = 2 + a'b` have positive `x_1`-degree, so both
products are hyperbolic.  Their axes join the two fixed points of each in
`P^1(K)`, the roots of `z^2 - a z - a/b` and of `z^2 - a' z - a'/b`
respectively; since `a != a'` these root pairs differ, so the axes are
distinct.  The unipotent `e_12(a)` fixes exactly one end, `infinity`, and
`e_21(b)` fixes exactly one end, `0`, so the group `Lambda_0` they generate
with `e_12(a')` fixes no end; it fixes no vertex (it contains hyperbolic
elements); and it preserves no line (an invariant line would be the axis of
every hyperbolic element of `Lambda_0`, but two hyperbolic elements have
distinct axes).  A group of tree automorphisms that fixes no vertex, fixes no
end and preserves no line contains a non-abelian free subgroup (ping-pong on
two hyperbolic elements with distinct axes, after passing to powers), so
`Lambda_0 <= E_r(R_+, I)` is non-amenable.  Two generators would not do when
`p = 2`, where `e_12(a)` and `e_21(b)` are involutions generating an infinite
dihedral group; the third generator is what forces distinct axes.  Hence
every non-central normal subgroup of `Gamma` is non-amenable, the amenable
radical is the finite center `Z = mu(F_q) cap EL_r`, and (4) applies.
