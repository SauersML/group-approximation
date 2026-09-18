---
rg: 2
id: mf-null-corner-criterion-needs-faithful-ce-trace-proof
kind: route
title: Cut the corona by the lifted corner projection, then compress the CE trace
target: mf-null-corner-criterion-needs-faithful-ce-trace
requires: []
---

Conventions are those of the target. `R^U` may be replaced by any tracial matrix ultraproduct
`prod_U (M_(d_n), tr)` throughout. Corners of such ultraproducts are again of this form (step C1), and every CE finite
von Neumann algebra embeds trace-preservingly in one.

## (A0) CE-null implies MF-null

Let `psi : B -> Q_k` be unital and let `U` be a free ultrafilter.

- The normalized traces `tr_(k_n)` vanish in the limit on the norm-null ideal.
- So `x -> lim_U tr_(k_n)(x_n)` is a well-defined tracial state on `Q_k`.
- It factors through the tracial ultraproduct `prod_U M_(k_n)`, so it is CE.
- Therefore `tau o psi` is a CE trace on `B`.

## (A) The corner criterion

**First part.** A unital `psi : q_z C[G] q_z -> Q_k` composes with `Phi` to a unital map `B -> Q_k`.

**Second and third parts.** Let `theta : C[G] -> Q_k` be a unital star homomorphism, and apply `theta` entrywise on
`M_n(C[G])`. Let `p` be a projection in `M_n(C[G])` whose corner is MF-null, and suppose `theta(p) != 0`.

- `M_n(Q_k) = Q_(n k)`.
- A nonzero projection in a norm matrix corona lifts to projections `p_j` of rank `r_j`. On an infinite set `S` of
  indices, `r_j > 0`: take a self-adjoint lift and the spectral cut at `1/2`, exactly as in
  `agent-leavitt-not-torsion-corner-noce-radical-proof`.
- Restriction to `S` is a surjective star homomorphism `Q_(n k) -> Q_(n k | S)`, and the image of `theta(p)` is still
  nonzero.
- The corner of `Q_(n k | S)` at that image is `prod_(j in S) p_j M p_j / directSum`, which is `Q_r` with `r = (r_j)`.
  This needs `||p_j x p_j|| = ||x restricted to p_j||`, which holds entrywise.
- So `theta` restricts to a unital map `p M_n(C[G]) p -> Q_r`, contradicting MF-nullity. Hence `theta(p) = 0`.

**Application to `p = q_z`.** Here `theta(z)` is a unitary with `theta(z)^m = 1`, and `1 - theta(q_z)` is its spectral
projection at `1`. So `theta(q_z) = 0` if and only if `theta(z) = 1`. As `theta` ranges over all norm-corona
representations, this gives `z in Rad_MF(G)`.

## (B) A hyperlinear host puts a CE trace on the corner

The canonical trace `tau_e` is faithful on `C[G]`. Moreover `tau_e(q_z) = 1 - (1/m) sum_(j<m) tau_e(z^j) = 1 - 1/m`,
because `tau_e(z^j) = 0` for `0 < j < m`.

- **Hyperlinear `G`.** Then `L(G)` is CE. For a projection `e` with `tau(e) > 0` in a CE algebra `(N, tau)`, the corner
  `(eNe, tau/tau(e))` is CE (step C1). So `tau_e / tau_e(q_z)` restricted to `D` is CE, and it is faithful because
  `tau_e` is.
- **General `sigma : C[G] -> R^U` with `sigma(z) != 1`.** The element `sigma(q_z)` is a nonzero projection. Since
  `tau_U` is faithful, `tau_U(sigma(q_z)) > 0`, and step C1 applies to `sigma(q_z) R^U sigma(q_z)`. So a CE-null `D`
  forces `sigma(z) = 1` for every such `sigma`, which is `z in Rad_hyp(G)`.

## (C) Stripping

**Step C1 (compression).** Let `e != 0` be a projection in `N = prod_U (M_(d_n), tr)`.

- Lift `e` to projections `e_n` with `tr(e_n) -> tau(e)`.
- Then `eNe = prod_U (e_n M_(d_n) e_n, normalized tr)`, with the trace scaled by `1/tau(e)`. This is again a tracial
  matrix ultraproduct.
- So any trace pulled back from `(eNe, tau/tau(e))` is CE.

**Step C2 (the quotient).** Let `tau = tau_U o pi` be a CE trace on the MF-null algebra `B`.

- If `psi : pi(B) -> Q_k` is unital, then `psi o pi : B -> Q_k` is unital. So `pi(B)` is MF-null.
- The trace `tau_U` is faithful on `pi(B)`.
- The kernel of `pi` is `{x : tau(x^* x) = 0}`.

**Step C3 (no CE-null corner).** Let `D` sit unitally in `R^U`, and let `p != 0` be a projection in `M_n(D)`, a
subalgebra of `M_n(R^U)`.

- `M_n(R^U)` is a tracial matrix ultraproduct, and `(tau_U tensor tr_n)(p) > 0`.
- Suppose a CE-null `A` has a unital map `A -> p M_n(D) p`. Composing with the C1 corner trace makes it CE, which is a
  contradiction.
- The same argument works in `M_n(L(G))` for hyperlinear `G`.

## The class consequence

Suppose MF-nullity of a witness `W`, a subalgebra of `C[G]`-corners, is certified by a unital map from a CE-null `A`
into a corner `p W p` with `p != 0`.

- Then, by C3 applied in `M_n(L(G))`, `G` is not hyperlinear.
- For every `sigma : C[G] -> R^U`, the same argument with `sigma(p)` in place of `p` forces `sigma(p) = 0`.

That is the death step named in the target, and it applies uniformly to every member.
