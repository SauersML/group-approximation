---
rg: 2
id: unitary-group-hosts-root-equivalence-proof
kind: route
title: Send free generators to generating unitaries, and embed a non-hyperlinear group in the unitary group of its own group factor
target: unitary-group-hosts-for-group-factor-universality-are-the-root
requires:
  - hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
---

**Item 1.**
- *Generation.* A separable tracial von Neumann algebra has a countable
  `||.||_2`-dense set of elements. Each element is a combination of four
  unitaries, so countably many unitaries `u_i` generate `N`.
- *`phi` is a character.* For `g, h in F_infinity`,
  `phi(h g h^(-1)) = tau(pi(h) pi(g) pi(h)*) = tau(pi(g))`. Also
  `sum_(i,j) conj(c_i) c_j phi(g_i^(-1) g_j) = tau(x* x) >= 0` for
  `x = sum_j c_j pi(g_j)`, and `phi(e) = 1`.
- *The GNS algebra is `N`.* The GNS representation of `phi` is unitarily
  equivalent to the left action of `pi(F_infinity)` on the closure of
  `span pi(F_infinity) Omega_tau` in `L^2(N, tau)`. That closure is all of
  `L^2(N)`, because the `u_i` generate `N` and `tau` is faithful and normal.
  So `pi_phi(F_infinity)''` is `N`.
- *`L(F_infinity)` is Connes-embeddable.* Free groups are residually finite,
  hence hyperlinear, so direction (1) ⟹ (2) of
  `hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower` applies.
- *The failing step.* If `N` is not Connes-embeddable, then `N` does not embed
  in `L(F_infinity)^omega` (an ultrapower of a Connes-embeddable algebra is
  approximable by matrices on separable subalgebras). This happens although
  `phi` realizes `N` from `F_infinity`. So realizing `M` by a character of `G`
  never gives an embedding of `M` into `L(G)^omega`. The only structure
  linking `M` to `L(G)` is the pair of characters `tau_M|_G` and `delta_e`,
  and these differ whenever some `g != e` has `tau_M(g) != 0`.

**Item 2.**
- *(a) ⟹ (b).*
  1. Let `Lambda` be a non-hyperlinear countable group and put `G = Lambda * Z`.
     `G` is not hyperlinear, since hyperlinearity passes to subgroups.
  2. `G` is ICC (free product of a nontrivial group with `Z`), so
     `M := L(G)` is a separable II_1 factor, and `g -> lambda(g)` embeds `G`
     as a subgroup of `U(M)`.
  3. By direction (2) ⟹ (1) of the dictionary node, `L(G)` is not
     Connes-embeddable.
- *(b) ⟹ (a).* If `L(G)` is not Connes-embeddable, direction (1) ⟹ (2) of the
  dictionary node, read contrapositively, shows `G` is not hyperlinear.
