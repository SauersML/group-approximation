---
rg: 2
id: km-l0-cohomology-is-the-49-orbit-invariants-complex
kind: claim
title: Low-degree cohomology of the lattice with any uniquely divisible coefficients is computed by the 49-orbit invariants complex
artifacts:
  - research/artifacts/km-lattice-cohomology-and-lp-fork-2026-08-23.md
distinct_from:
  km-thick-part-two-connected-and-lattice-is-f3: that establishes the topological input (the thick part is a 2-connected cocompact model); this converts it into a finite explicit cochain complex computing H^(<=2) for divisible coefficients, including the L^0 modules of Corollary E.
  km-group-ring-h2-vanishes-for-the-lattices: that computes the (non-divisible) integral group-ring coefficients by compactly supported cohomology; this handles arbitrary uniquely divisible modules by stabilizer-cohomology collapse instead.
  km-some-ergodic-action-has-nonzero-l0-second-cohomology: that is the open existence question; this is the established reduction making it a finite computation per action.
---

**THEOREM (established; proof in `km-l0-orbit-complex-proof`).**  Let
`Lambda = Lambda_(2,4,6)(q)`, `q > 1764^3`, and let `V` be ANY
`Lambda`-module whose underlying abelian group is uniquely divisible
(e.g. any `Q`- or `R`-vector space, in particular `L^0(Y,R)` of a
p.m.p. action).  Then for `n <= 2`

```text
H^n(Lambda; V)  =  H^n( C^0 -> C^1 -> C^2 -> C^3 ),
C^p = direct sum over the 49 cell orbits of X^/Lambda in dimension p
      of the invariants V^(P_J^+ cap P_K^-),
```

where the orbits of `p`-cells of the thick part `X^ = Z_(<=0)` are the
pairs `(J,K)` of PROPER subsets of `S = {1,2,3}` with
`|J| + |K| = 4 - p` (Birkhoff: a simplex pair lies in `X^` iff its
double coset `W_J w W_K` contains `1`, iff its reduced representative
is `w = 1`; `Lambda` is transitive on opposite chamber pairs), so the
orbit counts in dimensions `0,1,2,3,4` are `9, 18, 15, 6, 1`, and the
stabilizer of the standard `(J,K)` cell is the finite Birkhoff
intersection `P_J^+ cap P_K^- = T . <U_alpha : alpha in Phi_J^- cup
Phi_K^+>` (the root content is EXACT: `U_gamma` lies in the
intersection iff `gamma in (Phi^+ cup Phi_J^-) cap (Phi^- cup
Phi_K^+) = Phi_J^- cup Phi_K^+`), with Levi decomposition
`L_(J cap K) . (mixed unipotent part)` of order
`|L_(J cap K)(q)| . q^(N_J + N_K - 2 N_(J cap K))`, `N_J = |Phi_J^+|`
(`1` for rank one, `2, 4, 6` for `A_1 x A_1`, `B_2`, `G_2`); in
particular order `|T| . q^(N_J + N_K)` when `J cap K` is empty, and a
full rank-two finite Levi (e.g. the `G_2(q)`-type group at
`(J,K) = ({2,3},{2,3})`) on the diagonal.
Only dimensions `<= 3` (48 orbits) enter `H^2`.

Consequence: the `L^0` clause of Ioana--Spaas--Wiersma Corollary E
(`km-some-ergodic-action-has-nonzero-l0-second-cohomology`) is, for
each fixed action, the exactness question of an explicit finite
complex of invariant-function spaces.
