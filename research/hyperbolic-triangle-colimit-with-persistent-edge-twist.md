---
rg: 2
id: hyperbolic-triangle-colimit-with-persistent-edge-twist
kind: claim
title: A hyperbolic triangle colimit whose moment space survives every finite cover
distinct_from:
  persistent-degree-two-class-on-hyperbolic-group: that asks for any persistent class on a residually finite hyperbolic group; this asks for the explicit edge-twist classes of a triangle colimit, certified through the moment spaces of edge-twist-extensions-of-triangle-colimits-moment-test, and assumes no residual finiteness
  hyperbolic-triangle-of-finite-groups-not-virtually-torsion-free: that asks for torsion invisible in every finite quotient; this asks for a degree-two class on a triangle colimit that never dies in a finite cover, which kills residual finiteness of a central extension even when the colimit itself is virtually torsion-free
---

Exhibit a hyperbolic, virtually torsion-free colimit `Λ` of a triangle of finite groups
with trivial face group, and a prime `p`, such that the moment space `I_∞ <= F_p^3` of
`edge-twist-extensions-of-triangle-colimits-moment-test` is nonzero. Equivalently, some
2-cycle moment `c_12 μ_12 + c_23 μ_23 - c_13 μ_13` is nonzero on the 2-cycles of every
finite torsion-free normal cover. By (M6) of that node, some hyperbolic group is then not
residually finite.

**OPEN.**

## Attempts

- **Only `p`-covers can kill a moment** (M5). Transfer shows that covers of index prime
  to `p` do not change `I_N`. A persistence proof must therefore control the pro-`p`
  part of the finite-index subgroup lattice of one torsion-free `N`.
- **Where persistent classes must live.** The class must lie outside the image of
  continuous cohomology of the profinite completion
  (`finite-central-extension-rf-iff-virtually-splits`). So `N` must fail degree-2
  goodness at this class, and every hyperbolic virtually special group is good
  (`every-hyperbolic-group-is-good`, Attempts). Candidates therefore need (T) or some
  other obstruction to cubulation.
- **Cup products die.** If on some `N` the twist class is a cup product `h ∪ φ`, or a
  Bockstein `β(h)`, with `h in H^1(N;F_p)`, then pulling back to the `p`-cover defined by
  `h` kills it. This is the standard vanishing mechanism, recorded here as a heuristic:
  the Gysin-sequence argument was not written out. A persistent moment needs `N` whose
  classes in `H^2(N;F_p)` reached by twists are not profinitely visible, which is
  consistent with `H^1(N';F_p) = 0` along many covers.
- **Computation.** The test for one `N` is linear algebra of size `|Q| × 3|Q|/p` over
  `F_p`.
- **First-level data (2026-09-13, GAP 4.14 on MSI).** Scripts and raw outputs are in
  `experiments/edge-twist-moments/` (`moments.g`, `run1.g`, `run2.g`, `run1.out`,
  `run2.out`; `run1.out` predates the extra columns).
  - *Method.* Take random triples `x_12, x_13, x_23` of elements of prime order `p` in
    `Q = PSL(2,q)`. Form the coset triangle with vertex groups `<x_12,x_13>`,
    `<x_12,x_23>`, `<x_13,x_23>` and keep the hyperbolic ones (half-girths with
    `Σ 1/m_v < 1`). For `N = ker(Λ -> <x_12,x_13,x_23>)` compute:
    - `dim Z_N = |G| - rank(B)`, where `B` is the incidence matrix of right cosets
      against elements;
    - `dim I_N = rank([B; μ]) - rank(B)`;
    - `b_1(N;F_p)` from `χ(N\X) = 1 - b_1 + b_2`. It is printed only in `run2.out`;
      for `p = 3` the `run1.out` triples give `dim Z_N` and `dim I_N` only.
  - *Sanity check.* The Euler characteristic count gives an integer `b_1 >= 0` in every
    case.

  | `Q` | `p` | girths | `dim Z_N` | `b_1(N;F_p)` | `dim I_N` |
  |---|---|---|---|---|---|
  | `PSL(2,19)` (5 triples) | 5 | (6,8,8), (6,8,6), (6,6,8), (8,6,8), (6,8,6) | 1370 | 0 | 3 |
  | `PSL(2,29)` (2) | 7 | (8,8,8), (8,6,6) | 6962 | 0 | 3 |
  | `PSL(2,29)` (2) | 5 | (8,6,6) | 4874 | 0 | 3 |
  | `PSL(2,31)` | 5 | (6,10,10) | 5954 | 0 | 3 |
  | `PSL(2,27)` | 7 | (6,6,8) | 5618 | 0 | 3 |
  | `PSL(2,23)` (5 triples) | 3 | e.g. (16,14,8), (4,14,14) | 178–584 | 44–176 | 1–2 |

  In every hyperbolic coset triangle with `p >= 5`, all three vertex groups equal `Q`,
  `N` has no `F_p`-homology in degree 1, and no nonzero edge twist splits at the first
  level. So the cheap vanishing mechanism (cup products and Bocksteins from
  `H^1(N;F_p)`) is unavailable there. With `p = 3` there is plenty of `H^1`, and the
  moment space is already smaller.
- **Cartan–Leray filter (standard; not re-derived at chain level).** Let `N'' <= N` be
  normal in `Λ`, with `R = N/N''`. Pushing forward `H_2(N'';F_p) -> H_2(N;F_p)` is the
  edge map of `E^2_{s,t} = H_s(R; H_t(N'';F_p))`. Its cokernel is filtered by
  subquotients of `H_1(R; H_1(N'';F_p))` and `H_2(R;F_p)`. So `I_{N''} = I_N` unless `N`
  has a finite quotient `R` with `p`-torsion in `H_2(R;Z)`, or with
  `H_1(R; H_1(N'';F_p)) != 0`.

  For the `p >= 5` examples above, a persistence proof would therefore need exactly
  this: no finite quotient of `N` carries such `p`-local second homology along the
  tower. That is the concrete shape of the open problem for these explicit groups.
