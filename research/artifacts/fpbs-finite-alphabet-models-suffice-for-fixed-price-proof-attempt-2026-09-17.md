# Ergodic decomposition, product with Bernoulli, finite truncation of a near-optimal graphing and descent to the finite-partition factor

*Attempt artifact (2026-09-17), formerly route `fpbs-finite-alphabet-models-suffice-for-fixed-price-proof` into `fpbs-finite-alphabet-models-suffice-for-fixed-price`, requires [fpbs-clopen-certificate-cost-transfer, abert-weiss-free-actions-weakly-contain-bernoulli, cost-is-constant-on-weak-equivalence-classes]. Demoted from the graph because the referee vote of lens 1 was lost for this result; lenses 2 and 3 returned *survives*. No mathematical error has been reported. Restore it as a route once a full referee pass survives.*

Full written proof.

**Maximality.** By `abert-weiss-free-actions-weakly-contain-bernoulli`, `b ≺ a` for every free
p.m.p. action `a`, and by `cost-is-constant-on-weak-equivalence-classes` (finitely generated
`G`), `C(a) <= C(b)`. Nontrivial Bernoulli shifts are free, and any two weakly contain each
other by the same import, so `C(b)` does not depend on the base. Hence fixed price is
equivalent to `C(a) >= C(b)` for all free `a`. So 1 implies 2.

**2 implies 1.** Let `a = G ↷ (X, mu)` be free, and assume `C(a) < ∞` (otherwise there is
nothing to prove). Fix `S` a finite symmetric generating set.

*Step 1: ergodic components.* Let `mu = ∫ mu_e dP(e)` be the ergodic decomposition. For
`P`-a.e. `e`, `a_e = G ↷ (X, mu_e)` is free, since `mu(Fix gamma) = 0` for `gamma != 1` forces
`mu_e(Fix gamma) = 0` for a.e. `e`. A graphing generating the orbit relation of `a` generates
the orbit relation of `a_e` for a.e. `e`, since orbits lie in components. Its cost for `mu` is
the integral of its costs for `mu_e`. Hence `C(a) >= ∫ C(a_e) dP(e)`, and it suffices to treat
ergodic `a`.

*Step 2: product with Bernoulli.* Let `b = G ↷ (L^G, lambda^G)` with `|L| >= 2` and `a` ergodic.
Bernoulli shifts of an infinite group are mixing, so `a × b` is ergodic, and it is free. Lift a
generating graphing of `a` with pieces `gamma_j|D_j` to pieces `gamma_j|(D_j × L^G)`. A path
from `x` to `s.x` of product `s` lifts to a path from `(x, y)` to `s.(x, y)`, so the lift
generates with the same cost. Hence `C(a × b) <= C(a)`.

*Step 3: finite pieces.* Fix `eps > 0`. Run the first two paragraphs of item 2 of
`fpbs-clopen-certificate-cost-transfer-proof` on `a × b`; they use only freeness. This gives
finitely many Borel pieces `(gamma_j, D_j)`, `j <= N`, and a length `l` with
`sum_j (mu × lambda^G)(D_j) + sum_s (mu × lambda^G)(E_s) < C(a × b) + 2 eps`, where `E_s` is the
no-path set. Membership of `z` in `E_s` is a Boolean function of the memberships of the points
`g.z`, `g ∈ B_{lr}`, in the sets `D_j`.

*Step 4: descent.* Let `P` be the common refinement of the partitions `{D_j, D_j^c}` (`j <= N`)
and of the time-zero coordinate partition `zeta = {X × {y : y(1) = t} : t ∈ L}`. Let `K` index
the cells of `P`. The map `pi(z) = (g -> P-cell of g^{-1}.z)` is a `G`-equivariant factor map to
`K^G`. Let `nu = pi_*(mu × lambda^G)`. Then:

- `nu` is ergodic, as a factor of an ergodic action;
- `nu` is essentially free: composing `pi` with the map `K -> L` read off from `zeta` gives the
  factor map `(x, y) -> y` onto `lambda^G`, which is free, and a point fixed by `gamma` maps to a
  point fixed by `gamma`;
- each `D_j` is `pi^{-1}(C_j)` for a cylinder `C_j` over the identity window, and so each
  `E_s = pi^{-1}(N_s(Phi, l))` with `Phi = ((gamma_j, C_j))_{j <= N}`.

Hence `c_l(Phi, nu) < C(a × b) + 2 eps`, and item 1 of `fpbs-clopen-certificate-cost-transfer`
gives `C(nu) <= c_l(Phi, nu)`. By hypothesis 2, `C(b) <= C(nu) < C(a) + 2 eps`. So `C(a) >= C(b)`,
and with maximality `C(a) = C(b)`.
