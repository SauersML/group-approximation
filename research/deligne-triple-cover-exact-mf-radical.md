---
rg: 2
id: deligne-triple-cover-exact-mf-radical
kind: claim
title: The MF radical of Deligne's triple cover is exactly its order-three center
goal: true
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
distinct_from:
  deligne-triple-cover-finite-residual-is-center: that computes the intersection of kernels of finite quotients; this computes the smaller intersection of kernels of all norm-matrix-corona representations.
  deligne-triple-cover-central-generator-is-mf-radical: that is the hard inclusion C_3 <= Rad_MF(E_3); this packages it with the unconditional reverse inclusion to give the exact radical.
---

For Deligne's connected triple cover

```text
1 -> C_3 -> E_3 -> Sp_4(Z) -> 1
```

one has

```text
Rad_MF(E_3) = C_3.                                     (DER1)
```

In particular, for either generator `z` of `C_3`,

```text
z in Rad_MF(E_3).                                      (DER2)
```

## Attempts

- The reverse inclusion is unconditional:
  `Rad_MF(E_3) <= Res_fin(E_3)=C_3`.  The forward inclusion is exactly
  `deligne-triple-cover-central-generator-is-mf-radical`.
- Because `C_3` has prime order and the universal MF quotient detects
  triviality of the radical, `(DER1)` is equivalent to the open claim that
  `E_3` is not MF.  Finite-dimensional invisibility alone does not establish
  this asymptotic operator-norm assertion.
- `deligne-triple-cover-mf-radical-dichotomy` now records the unconditional
  result: the radical is either `1` or the order-three covering kernel
  `C_3`.  The nontrivial branch is equivalently the open point-norm sector
  exclusion `deligne-nontrivial-maslov-opnorm-sectors-are-empty`.
- **2026-09-18, swarm-0917-w7-w7-deligne-break: Dadarlat's windings do not refute the flagship; new split.**
  `sp4-quasirep-windings-budget-and-saturation` (established) shows that normalized Maslov windings of
  `Sp_4(Z)` quasi-representations are at most `(6g-1) eps/4`, and that `P_op = R/Z` forces them to reach linear
  order. Dadarlat's nonzero windings only give `S_W > 0`, so they are compatible with both branches. The flagship
  follows from the open `sp4-quasirep-windings-are-sublinear` (which gives `P_op = (1/m)Z/Z`) together with the
  open `deligne-finite-parameter-group-has-period-prime-to-three` (`3 not | m`). This is route
  `deligne-triple-cover-via-sublinear-windings`.
- **2026-09-18, swarm-0917-w7-w7-deligne-last1 (calibration): the last
  mile is blocked, and the manuscript's own mechanism is provably silent.**
  - *Blocked routes.* Both shortest routes end in one open leaf, and each
    leaf is at least flagship-hard:
    - LLP route: `sp4-mod3-twisted-fibres-have-llp` implies the HS gap,
      hence non-hyperlinearity of `E_3`. It also implies the open LLP of
      `C*(F2 x F2)` (`mod3-twisted-fibre-llp-forces-f2xf2-llp`).
    - MH1 route: `maslov-diverging-positive-lifts-have-vanishing-high-degree-mass`
      is equivalent to the HS gap
      (`high-degree-range-mass-is-exactly-tracial-ucp-liftability`).
  - *Class killed.* `deligne-cover-compression-defects-are-trivial`
    (ESTABLISHED) proves `D(Delta, L) = 1` for every subgroup `Delta` of
    every Deligne cover `Gamma_n` of `Sp_(2g)(Z)` and every `L <= Delta`.
    The same holds for every central quotient of `E_3` that keeps `z`.
    - Every compression-defect non-MF criterion therefore dies at "exhibit
      `1 != w in D(E_3, L)`". This covers normal-Kazhdan, finite-normal,
      central-defect-element, locally-finite, mark-stability and the
      manuscript's compression criterion.
    - The kill holds for Kazhdan or non-Kazhdan `L`, thin or arithmetic.
    - The invariant is the Guichardet--Wigner quasimorphism
      (`sp2g-central-commutators-of-universal-lifts-are-torsion`).
  - *Consequence for decomposition.* A thin rigid subgroup
    (`sp4-deligne-rigid-infinite-index-subgroup-exists`) cannot be exploited
    through compression. Any proof of `(DER2)` must use operator-norm data
    that no source-side commutator identity encodes, or pass through an
    overgroup with an extension theorem.
- **2026-09-18, swarm-0917-w8-w8-deligne-break (operator-algebras): the full-circle alternative is killed by non-MF of
  Deligne's lattice; new split.** See `deligne-lattice-non-mf-forces-finite-parameter-group` (ESTABLISHED).
  - *One direction outright.* One irrational norm-parameter, glued to the residually finite base, gives an injective
    corona model of `Gamma~ = E_infinity`. So "`Gamma~` is not MF" implies `P_op = (1/m)Z/Z`.
  - *Radical dichotomy.* On the finite branch, `Rad_MF(Gamma~)` is `{1}` or exactly `<z^m>`.
  - *Arc constraint.* On the finite branch, a corona model with `Theta(z)^m != 1` must put a nondegenerate arc of
    `sp(Theta(z))` through a point off `mu_m`, with no commutant corner localizing there. So models with finite or
    totally disconnected central spectrum never separate `z^m`.
  - *Conditional converse.* Under the single instance `(CPE*)` of `commutant-projection-extraction` at
    `(Gamma~, z^m)`: `Gamma~` is MF iff `P_op = R/Z` iff every `E_q` is MF.
  - *New split.* Route `deligne-triple-cover-via-deligne-lattice-non-mf` needs two prerequisites, each of which can
    fail on its own:
    - `deligne-universal-cover-lattice-is-not-mf` (OPEN), a statement about one torsion-free-up-to-finite-index
      Kazhdan lattice, which is equivalent to the same statement for `Gamma~(3)`;
    - `deligne-finite-parameter-group-has-period-prime-to-three`.
    Under `(CPE*)`, the flagship implies the first prerequisite.
  - *Not pursued.* Virtual descent to kill the prime three duplicates the DEAD result of swarm-0917-w8-w8-deligne-last1
    on the period claim. The divisibility set `{+-1, +-2}` preserves `(1/6)Z`.
- **2026-09-18, swarm-0917-w9-w9-deligne-break (operator-algebras): reduced-algebra routes die, in both directions, at
  "`C*_r(Sp_4(Z))` is MF".** See `deligne-twisted-reduced-mf-iff-group-mf-and-sp4-reduced-mf` (ESTABLISHED).
  - *Theorem.* For rational `theta`, `C*_r(Gamma, c_theta)` is MF iff `theta in P_op` and `C*_r(Gamma)` is MF.
    Likewise `C*_r(E_q)` is MF iff `E_q` is MF and `C*_r(Gamma)` is MF. Invariant: Fell absorption,
    `Theta ⊗ lambda_tau ~ 1 ⊗ lambda_(c tau)`, combined with exact-MF tensor permanence and `A^op ≅ C*_r(Gamma, c^-1)`.
  - *Class killed.* Any refutation by reduced-norm-faithful `1/3`-models (strong convergence, or an MF embedding of
    `C*_r(E_3)`) also makes `Sp_4(Z)` an infinite Kazhdan group with MF reduced algebra, which is the open root
    `infinite-kazhdan-group-with-mf-reduced-cstar`. Any proof through non-MF of `C*_r(Gamma, c_(1/3))` is valid only
    alongside that same open statement.
  - *New split.* flagship `<=` [`C*_r(Sp_4 Z, c_(1/3))` not MF] and [`C*_r(Sp_4 Z)` MF]. Each prerequisite can fail
    on its own. Surviving routes must use non-tempered finite-dimensional structure.
- **2026-09-18, swarm-0917-w13-w13-deligne-break (finite-models): torsion-point duality for induced
  Torelli characters. Refutation route not found; floor reduced to short positive relations.**
  - A refutation would need honest `Mod(S_2)`-representations with a separating twist near `omega I`.
    The candidate class was `Ind_Lambda^M phi` with `Lambda >= I`.
  - `mod-s2-induced-torelli-characters-have-positive-relation-floors` (ESTABLISHED) shows three things.
    Their defect is exactly `(1/3) min ||psi||_B` over integral `psi = chi mod 3` on
    `B = im H_2(Gamma')`. Any relation `b in B` with `3 not| chi(b)` gives the floor `1/(3||b||_1)`. The
    base value is `1/15`.
  - Where the known mechanism dies: the only positive relations constructed are transfers, with
    `chi = 5[Sp_4(Z):Gamma']`, which vanish mod 3 on every index divisible by 3.
  - Uniformity of this class is now `mod-s2-torelli-positive-relations-have-bounded-mass` (OPEN).
  - This class cannot refute the flagship unless `A_+ -> infinity`. The class stays open, but it is now
    a combinatorial question about short positive products of separating twists.
- **2026-09-18, swarm-0917-w13-w13-deligne-follow (reframing): the monomial gate splits into a slope condition and a
  period condition.** See `deligne-monomial-parameter-group-is-governed-by-maslov-slope` (ESTABLISHED, unreviewed).
  - *Theorem.* Let `m(t) = inf_X mu_t(X)` be the best uniform relator defect of monomial `t`-models over finite
    `Sp_4(Z)`-sets. It is subadditive and even, and it is `1/2`-periodic by Deligne's residual `2Z` and the Weil
    double cover.
    - Its zero set `P_mon` is a closed subgroup with `(1/2)Z/Z <= P_mon <= P_op`.
    - The slope `s = lim_(t->0) m(t)/t` exists and equals `sup_t m(t)/t`. So `P_mon = R/Z` iff `s = 0`.
    - `m(1/3) = m(1/6) <= mu_t(X)/(6t) + c_K t` for every `X` and every `t <= 1/6`.
  - *New split.* The uniform third cellular floor `m(1/3) > 0` is necessary for the flagship. It holds iff two
    conditions hold, each of which can fail on its own:
    - (A) `s > 0`, i.e. `P_mon` is finite;
    - (B) if `P_mon` is finite, `3` does not divide `|P_mon|`.

    (A) is implied by the output of `sp4-quasirep-windings-are-sublinear`. (B) is implied by that output together
    with `deligne-finite-parameter-group-has-period-prime-to-three`. So each operator-norm prerequisite of the
    sublinear-windings route has a monomial shadow, which is a finite cellular-lattice question.
  - *Refutation handle.* Any family of monomial models at small parameters `t_n -> 0` with defect `o(t_n)` refutes
    the flagship. The target is a Diophantine one: find integral classes on Schreier complexes that approximate
    `t kappa_R` better than linearly.
  - *Not decided.* The value of `s` is not decided, nor is (B). A uniform systole of the integral lattices `L_X`
    would force `s = c_K`.
  - *Checked against the graph.* Bounded-mass detecting-cycle certificates are already known to die along the
    congruence tower (the systole grows; see `deligne-class-finite-action-norms-vanish`), so they are not repeated
    here.
- **2026-09-19, swarm-0917-w18-w18-deligne-break (calibration).** See
  `sl2-half-triple-cover-mf-iff-twisted-iwahori-opnorm-matching`, whose Theorems A-D are proved there.
  - *Setting.* The twin world is `G = SL_2(Z[1/2])`, which has no property T, with Deligne-type covers
    `W_m = G~/<z^m>`.
  - *Criterion (Theorem A).* `W_m` is MF iff `Delta(pi/m) = 0`. Here `Delta(theta)` is the infimum, over pairs of
    exact unitary `PSL_2(Z)` representations, of the operator-norm defect of the twisted Iwahori square-root gluing
    `SR ~ gamma (sr)^2`, `s r^-1 ~ gamma^-1 (S R^-1)^2`, with `gamma = e^(-i theta/6)`.
  - *Structure.* `Z(Delta)` is a closed subgroup containing `pi` (exactly, via `SL_2(F_3)`). The determinant winding
    gives `delta_n(pi/3) >= 2 sin(dist(n pi/18, (pi/3) Z)/(2n))`.
  - *Belief change.* The natural guess `Delta(pi/3) = 2 sin(pi/36) = 0.1743` is the scalar optimum, and it is sharp
    for `n <= 3`. It is **false**. Mixing exact `theta = pi` and `theta = 0` pieces of the `SL_2(F_3)` permutation
    representation in the ratio 1 : 2 cancels the winding obstruction, and gives a certified `n = 12` witness with
    `delta = 0.13265`.
  - *What it means here.* The finite-`n` winding (first Chern class, the twin of
    `deligne-triple-cover-via-sublinear-windings`) is not a rigid obstruction in the property-T-free twin. Any
    argument for this flagship that does not use a feature of `Sp_4(Z)` absent from `SL_2(Z[1/2])` must also decide
    `Delta(pi/3)`.
  - *Not decided.* Whether `Delta(pi/3) = 0` remains open.
