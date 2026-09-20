---
rg: 2
id: mod-s2-normal-level-torelli-floors-are-coupled
kind: claim
title: At normal levels of Sp_4(Z) the separating-twist winding floor e and the cube-root floor d are pinned by the same two numbers of the relation lattice, so e(Gamma(N)) = 3 d(Gamma(N)) at N = 1, 2, 3, 4 and a uniform sparse certificate for (TAP) also proves (Z) on Torelli-abelian representations
distinct_from:
  mod-s2-monomial-torelli-windings-census: that defines e, proves (MW1)-(MW3), and computes e on 35 levels, all but one of them non-normal, missing Gamma(3) and Gamma(4); this proves the lower bound e >= 1/L from a single W-vector (no span condition) at normal levels, which gives the new exact values e(Gamma(3)) = 1/5 and e(Gamma(4)) = 1/10 from existing data. It also shows that the level-dependence recorded there (1/7 at line-6) is an effect of non-normal levels.
  mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit: that is the cube-root floor d and its certificate (TA3), which needs no normality; this couples d to the winding floor e on the same lattice at normal levels.
  mod-s2-gamma4-torelli-census-is-one-thirtieth: that computes W(Gamma(4)) and d(Gamma(4)) = 1/30; this reads the winding floor e(Gamma(4)) = 1/10 off the same transversal relation.
  mod-s2-near-identity-torelli-windings-vanish: that is the open statement (Z) for all representations; this proves nothing unconditional about (Z) in the limit, and shows instead that the sparse-certificate mechanism for (TAP) would prove (Z) on the Torelli-abelian class, and so on finite-image representations.
  mod-s2-torelli-abelian-census-limit-is-positive: that is (TAP), d_inf > 0; this proves no bound on d_inf. It shows that the uniform-certificate route to (TAP) also bounds e_inf, and that g(Gamma(N)) -> infinity would kill both limits at once.
artifacts:
  - experiments/mod-s2-normal-level-coupling-2026-09-17/check_normal_levels.py
  - experiments/mod-s2-normal-level-coupling-2026-09-17/normal-levels.json
---

**ESTABLISHED** through `mod-s2-normal-level-torelli-floors-coupling-proof`. Unreviewed; no novelty
claimed.

**Notation.** As in `mod-s2-monomial-torelli-windings-census` and
`mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`.
- `M = Mod(S_2)`, `pi : M -> Gamma = Sp_4(Z)`, `t_s` a separating twist.
- `Gamma'` has finite index, and `M' = pi^(-1)(Gamma')`.
- `v_j` are the distinct separating-twist classes in `H_1(M')`, with multiplicities `mult_j`.
- `W = W(Gamma')` is the relation lattice, `W^*` its dual, and `chi(w) = sum_j w_j` the augmentation.
- `e(Gamma')` is the winding floor of (MW1), and `d(Gamma')` is the cube-root floor of (TA1). Here `d`
  is the same quantity as `D` of `mod-s2-induced-torelli-characters-have-positive-relation-floors`.

Three lattice numbers:
```text
g(Gamma')   = gcd { chi(w) : w in W }                         (5 | g and 3 not| g, recorded on the TAP node)
m_0(Gamma') = min { ||w||_1 : w in W, chi(w) != 0 }
m_3(Gamma') = min { ||w||_1 : w in W, 3 not| chi(w) }          (so g <= m_0 <= m_3)
```

## Statement

1. **(N1) Orbit certificates at normal levels.** Let `Gamma'` be normal in `Gamma`. Then the multiplicity
   vector `mult` is constant, and for every `w in W` with `chi(w) != 0`,
   ```text
   sum_(x in M/M') x . w  =  chi(w) mult ,     hence     e(Gamma') >= 1/||w||_1 .
   ```
   Consequently `e(Gamma') >= 1/m_0(Gamma')`. This is (MW3) with its span hypothesis replaced by a single
   vector.
2. **(N2) Upper bounds at every level.** For every `Gamma'`, `e(Gamma') <= 1/g(Gamma')` and
   `d(Gamma') <= 1/(3 g(Gamma'))`, both attained by constant vectors.
3. **(N3) Sandwich.** At a normal level,
   ```text
   1/m_0 <= e <= 1/g ,        1/(3 m_3) <= d <= 1/(3 g) .
   ```
   If `W` contains a **tight** vector, i.e. one with `||w||_1 = |chi(w)| = g` (a sign-constant relation of
   minimal augmentation), then `e = 1/g` and `d = 1/(3g)`, so `e = 3d`.
4. **(N4) New exact values.**
   - `e(Gamma(3)) = 1/5`. `Gamma(3)` has index 51840. The windings census did not reach it: the run was
     killed for memory.
   - `e(Gamma(4)) = 1/10`. `Gamma(4)` has index 737280.
   - `e(Gamma') = 1/10` for every `Gamma(4) <= Gamma' <= Gamma(2)`, and `e(Gamma') >= 1/10` for every
     `Gamma' >= Gamma(4)`.

   With the census values at `N = 1, 2`, at every principal level computed so far:

   | `N` | `g` | tight vector | `e(Gamma(N))` | `d(Gamma(N))` |
   |---|---|---|---|---|
   | 1 | 5 | `5` on one class | 1/5 | 1/15 |
   | 2 | 10 | all ones on 10 classes | 1/10 | 1/30 |
   | 3 | 5 | `-1` on a `GQ(2,4)` point star (5 classes) | 1/5 | 1/15 |
   | 4 | 10 | a transversal relation (10 classes) | 1/10 | 1/30 |

   The table has `e = 3d = 1/g` in every row.
5. **(N5) Uniform coupling.** Put `L = sup_N m_3(Gamma(N))`. If `L < infinity`:
   - `d_inf >= 1/(3L)`, which is (TAP);
   - `e_inf >= 1/L`, so (Z) holds on all Torelli-abelian representations with `eta_0 = 2 sin(pi/L)`;
   - (Z) holds on all finite-image representations with `||rho(t_s) - 1|| < min(1/2, 2 sin(pi/L))`.

   `mod-s2-torelli-positive-relations-have-bounded-mass` (`sup A_+ < infinity`) implies `L < infinity`,
   since `A_+ >= m_3`.

   Conversely, if `g(Gamma(N)) -> infinity` along divisibility, then `e_inf = d_inf = 0`. So
   `sup_N g(Gamma(N)) < infinity` is necessary both for (TAP) and for (Z) on Torelli-abelian
   representations.

## What this changes

- **The census reading "e moves with the level, d does not" is an artifact of non-normal levels.**
  - `mod-s2-monomial-torelli-windings-census` records `e = 1/7` at `line-6` and at `flag-2 cap flag-3`,
    against `d in {1/15, 1/30}` everywhere. From this it concludes that the two floors behave differently
    under deepening.
  - Both limits are limits along `Gamma(N)`, by (MW2) and (TA2), and the principal levels are normal.
  - At normal levels, (N1) forbids the line-6 phenomenon. There, `w_2 = (0,2,2,1,0)` has `l1 = chi = 5`
    and yet `e = 1/7 < 1/5`, which (N1) would exclude at a normal level.
  - On all four principal levels known, the floors are locked, with `e = 3d`.
- **The two halves of the genus-two program pull against each other.**
  - The flagship needs (TAP), a necessary condition recorded on `mod-s2-torelli-abelian-census-limit-is-positive`.
  - The gate route `deligne-opnorm-sectors-empty-via-mod-s2-matricial-stability` needs (Z) to fail, via
    `mod-s2-instability-via-vanishing-torelli-windings`.
  - By (N5), the mechanism proposed for (TAP), uniformly sparse relations at principal levels, would also
    prove (Z) on every Torelli-abelian representation and, through
    `mod-s2-finite-image-near-scalar-reps-are-torelli-abelian`, on every finite-image representation.
  - So if (TAP) is proved that way, any counterexample to (Z) must be an infinite-image representation
    with nonabelian Torelli image. Matricial stability of `M` can then only come from such
    representations.
- **A single test decides both floors at the next principal level.** At each new `Gamma(N)` it suffices to
  find:
  - the gcd `g`;
  - one sign-constant relation of augmentation `g`, i.e. `g` separating twists whose product is trivial in
    `H_1(M_N)`.

  The `GQ(2,4)` point stars at `N = 3` and the transversal relations at `N = 4` are exactly such relations.
  If they persist, `e = 3d = 1/g` at that level.

## What is not claimed

- No value or positive lower bound for `e_inf` or `d_inf`.
- Nothing about non-Torelli-abelian representations.
- `L < infinity` is not proved. It is at least as strong as the uniform-certificate route to (TAP).
- `e(Gamma(6))` and higher levels are not computed. Only `e(Gamma(6)) <= 1/10` follows from (MW2).
