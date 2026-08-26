---
rg: 2
id: remainder-corner-monomial-free-proof
kind: route
title: Uniqueness of the extremal decomposition transports trivial masses; transvections give equality on monomials; nested events force zero
target: remainder-corner-fiber-kernels-are-monomial-free
requires:
  - remainder-corner-root-character-is-persistently-nonregular
  - kt-remainder-corner-characters-are-infinite-index-induced
  - model-characters-of-compressed-pairs-are-compression-invariant
---

**(1) Transport.**  Tracial states of `C^*(Gamma)` form a Choquet simplex,
so `chi = int chi_omega dmu(omega)` is unique (`mu` a probability measure on
the standard Borel space of extremal characters).  Each `chi_omega o phi_A`
is again a normalized tracial positive-definite function, with its own
decomposition measure `nu_omega`.  The measure `mu' = int nu_omega dmu(omega)`
satisfies `int chi' dmu'(chi') = int (chi_omega o phi_A) dmu = chi o phi_A
= chi` (`model-characters-of-compressed-pairs-are-compression-invariant`),
hence `mu' = mu` by uniqueness.  For `g in Gamma` let
`Omega_g = {chi' : chi'(g) = 1}`.  A mixture `int chi' dnu` takes the value
`1` at `g` iff `chi'(g) = 1` for `nu`-a.e. `chi'` (all values lie in the
closed unit disc), so `nu_omega(Omega_g) = 1` whenever
`chi_omega(phi_A(g)) = 1`.  Therefore
`Psi(g) = mu(Omega_g) = int nu_omega(Omega_g) dmu(omega) >= mu{omega :
chi_omega(phi_A(g)) = 1} = Psi(phi_A(g))`.

**Identification on root subgroups.**  `ker pi_(chi_omega)` is normal in
`Gamma`, and for a normal subgroup `N` of `E_r(R_+)` with sandwich ideal `J`
one has `N cap U_ij = e_ij(J)` (`E(R_+, J) <= N <= C(R_+, J)`), so
`{f : chi_omega(e_ij(f)) = 1} = J_omega` is the kernel ideal and
`m(f) = mu{omega : f in J_omega}`.  As `J_omega` is an ideal,
`m(f) <= m(f h)` for all `h`.

**(2) Constancy on monomials.**  For a transvection `T = 1 + E_ij` and
`v in N^d`, `T v = v + v_j e_i >= v` coordinatewise, so `x^(Tv)` is a multiple
of `x^v` and `m(x^(Tv)) >= m(x^v)`; while (1) with `g = e_kl(x^v)` gives
`m(x^(Tv)) = Psi(phi_T(e_kl(x^v))) <= m(x^v)`.  Hence `m(x^(Tv)) = m(x^v)`,
and applying this to `v - v_j e_i` when `v_i >= v_j` gives
`m(x^(v - v_j e_i)) = m(x^v)`: `m` is constant along Euclidean steps on any
pair of coordinates.  Now run the connectivity argument of
`remainder-corner-root-character-nonregular-proof` (4) with inequalities:
for `v != 0` with `v_i >= 1`, `m(x^v) <= m(x^(v + e_j))` (divisibility), then
Euclidean equalities on `(i, j)` from `(v_i, 1)` reach a vector with
`i`-th coordinate `0` and `j`-th coordinate `1`, and further steps reach
`e_j`; so `m(x^v) <= m(x^(e_j))`, and symmetrically `m(x^(e_i)) <= m(x^(e_i + e_k))
= m(x^(e_k))` for all `i, k`, so all `m(x^(e_k))` are equal, `=: m_0`; and
for any `v != 0`, `m_0 = m(x^(e_k)) <= m(x^v) <= m_0` for a coordinate `k`
with `v_k >= 1`.

**(3) Zero.**  The events `Omega_v = {omega : x^v in J_omega}` are nested,
`Omega_v subseteq Omega_(v+w)`, with equal measure `m_0`, hence equal up to
null sets; over the countably many pairs, for a.e. `omega` either no
monomial or every nonzero monomial lies in `J_omega`.  In the second case
`J_omega` contains the augmentation ideal, so `E(R_+, J_omega) <= ker
sigma_omega <= N_omega` has finite index, contradicting
`[Gamma : N_omega] = infinity` on the remainder corner.  So the second case
is null and `m_0 = 0`.
