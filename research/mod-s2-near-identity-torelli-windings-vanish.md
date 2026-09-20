---
rg: 2
id: mod-s2-near-identity-torelli-windings-vanish
kind: claim
title: An honest representation of Mod(S_2) whose separating twist is operator-norm close to the identity has zero trace-log on that twist
distinct_from:
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that asks that the spectrum of a separating twist never concentrates near a primitive cube root; this allows concentration near 1 and asks that the eigen-angles then sum to zero.
  mod-s2-stability-forces-honest-torelli-windings: that is the established implication from stability to nonzero near-identity windings; this is the open statement that would contradict it.
  sp4-quasirep-windings-are-sublinear: that bounds windings of all quasi-representations of Sp_4(Z) by o(defect) after normalizing by dimension; this is an exact vanishing statement, without normalization, for the special quasi-representations of Sp_4(Z) induced by honest representations of Mod(S_2).
---

**OPEN.** Notation as in `mod-s2-stability-forces-honest-torelli-windings`. There is `eta_0 > 0` such that
every finite-dimensional unitary representation `rho` of `M = Mod(S_2)` with
`||rho(t_s) - 1||_op < eta_0` satisfies

```text
kappa(rho(t_s)) = (1/2 pi i) Tr log rho(t_s) = 0 .                      (Z)
```

Since `kappa(rho(t_s))` lies in `(1/10)Z`, (Z) is equivalent to: there is no sequence of honest
representations `rho_n` with `||rho_n(t_s) - 1|| -> 0` and `kappa(rho_n(t_s)) != 0`. By (TW1), (Z) says
exactly that the `Sp_4(Z)`-quasi-representations induced by honest `M`-representations near the Torelli
identity have zero Dadarlat winding.

**Why it matters.** (Z) refutes `mod-s2-is-point-norm-matricially-stable` through route
`mod-s2-instability-via-vanishing-torelli-windings`, and so kills the genus-two gate route
`deligne-opnorm-sectors-empty-via-mod-s2-matricial-stability` as filed. The failure of (Z) is a necessary
condition for that route.

**How it can fail.** Honest representations with infinite image in which a separating twist has
`d_n -> infinity` eigen-angles `theta_j`, all tending to `0`, with `sum theta_j = 2 pi kappa`,
`kappa in (1/10)Z \ {0}` fixed. Dimension counting permits this: it needs `d_n >= 2 pi |kappa| / eta_n`.

## Attempts

- **2026-09-18, swarm-0917-w10-w10-deligne-last1: finite image gives only a per-representation floor
  (sketch, not a proof).** Let `rho` have finite image with kernel `N`, `Lambda = pi(N)`, of index `D`.
  Choose lifts of generators of `Lambda` inside `N`. Then every relator word of `Lambda` lies in
  `N cap K` and maps to `1` under `rho`. Write the Hopf word of `tr x in H_2(Lambda;Z)` as a product of
  `L_Lambda` conjugates of `t_s^(+-1)`; its exponent sum is nonzero (its image under the extension
  homomorphism of Step 0 is `D k`). Step 2 of the proof route then gives `kappa(rho(t_s)) = 0` as soon as
  `L_Lambda ||rho(t_s) - 1|| < 2`. The bound `L_Lambda` grows with `Lambda`, so this is the same
  non-uniform floor as (E4) in `mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors`. It does not
  prove (Z), and it says nothing about representations with infinite image (quantum representations and
  their relatives).
- **2026-09-20, swarm-0917-w23-w23-deligne-break: at normal levels the winding floor is locked to the
  cube-root floor (established side result, not a proof of (Z)).** See
  `mod-s2-normal-level-torelli-floors-are-coupled`.
  - *The mechanism.* At a normal level, averaging one relation `w` over `M/M'` gives
    `chi(w) mult`. So `e(Gamma') >= 1/||w||_1` for any single `w in W` with `chi(w) != 0`, with no span
    hypothesis. Constant vectors give `e <= 1/g` and `d <= 1/(3g)`.
  - *New exact values.* `e(Gamma(3)) = 1/5` and `e(Gamma(4)) = 1/10`, both read from existing census data.
    With `N = 1, 2`, every principal level known has `e = 3d = 1/g`.
  - *The census reading.* The `1/7` values in `mod-s2-monomial-torelli-windings-census` come from
    non-normal levels. They say nothing about `e_inf`, which is a limit along `Gamma(N)`.
  - *What would decide it.* A uniform bound `L` on sparse relations with `3 not| chi` at principal levels
    would give (TAP) and also (Z) on all Torelli-abelian representations, hence on all finite-image ones,
    with `eta_0 = min(1/2, 2 sin(pi/L))`.
  - *What it means for the (Z)-failure route.* A counterexample to (Z) keeps the matricial-stability gate
    route alive. If (TAP) falls to that mechanism, such a counterexample needs infinite image and
    nonabelian Torelli image.
  - *Where it dies.* No bound on `L` or on `g(Gamma(N))` beyond `N = 4`. Nothing about
    non-Torelli-abelian representations.
