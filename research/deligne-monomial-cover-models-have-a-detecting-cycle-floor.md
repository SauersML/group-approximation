---
rg: 2
id: deligne-monomial-cover-models-have-a-detecting-cycle-floor
kind: claim
title: A twisted permutation model of a finite Deligne cover over an exact finite quotient has normalized relator defect at least 4 nu / A for any detecting 2-cycle of mass A
distinct_from:
  deligne-monomial-twisted-modules-have-no-folner-truncations: that excludes coordinate Folner truncations of one infinite monomial module over finite fields; this bounds the normalized HS defect of finite monomial unitary models with arbitrary real phases over an exact finite Gamma-set, in terms of a 2-cycle invariant of the quotient complex.
  maslov-bounded-block-sector-gap: that bounds the mass carried by bounded invariant blocks; monomial models over large transitive Gamma-sets typically have no bounded blocks, and this floor needs none.
  deligne-symplectic-covers-are-not-schatten-approximated: that gives the floor delta d^(-1/2) for all tuples at g >= 3 from Frobenius stability; this uses no stability theorem, holds at every genus including the genus-two witness, and is sharper whenever the detecting cycles are small.
---

**ESTABLISHED** (`deligne-monomial-cover-models-detecting-cycle-floor-proof`). Unreviewed.

**Setting.** `Gamma = <S | R>` finitely presented, with a central extension whose lifted
presentation has `r~(S) = z^(k_r)` for `r in R` and `z` central; `Gamma_n` is its quotient by
`z^n = 1`. For the Deligne covers of `Sp_(2g)(Z)`, `g >= 2`, `k` represents the covering class.
Fix `zeta = exp(2 pi i theta)` with `zeta^n = 1`.

A **monomial model over a finite Gamma-set `X`** is `rho(z) = zeta I` and `rho(s) = D_s P_s` on
`l^2(X)`. The permutations `P_s` define an *exact* action of `Gamma` on `X`, and `D_s` is diagonal
with entries `exp(2 pi i a(x, s))`. Put `d = |X|` and
`eta_r = ||rho(r~(S)) zeta^(-k_r) - I||_HS`, normalized.

`Y_X` is the 2-complex with vertices `X`, an edge `x -> s.x` for each `s`, and a 2-cell `(x, r)`
along the loop reading `r` at `x`. An integral 2-cycle `Sigma = sum n_(x,r) (x, r)` has **mass**
`|Sigma|_1 = sum |n_(x,r)|`, and is **detecting** if
`nu(Sigma) = dist(theta sum n_(x,r) k_r, Z) > 0`.

**Theorem.**
1. **Normal quotients.** If `X = Gamma/N` with `N` normal of finite index, then for every
   detecting integral 2-cycle `Sigma` on `Y_X`,

   ```text
   max_(r in R) eta_r >= 4 nu(Sigma) / |Sigma|_1.                         (MCF1)
   ```

2. **Any transitive quotient.** If `X = Gamma/Lambda`, `(MCF1)` holds with `Sigma` on `Y_(Gamma/N)`,
   `N` the normal core of `Lambda`.
3. **Any finite Gamma-set.** If the orbits `X_i` have normal cores `N_i`, then
   `max_r eta_r >= 4 |R|^(-1/2) min_i nu(Sigma_i)/|Sigma_i|_1` for detecting `Sigma_i` on
   `Y_(Gamma/N_i)`.
4. **Detecting cycles exist.** For the Deligne covers `Gamma_n`, `n >= 3`, and `zeta^2 != 1`, every
   `Y_(Gamma/N)` carries a detecting cycle. Otherwise some exact monomial model would send `z` to
   `zeta I`, contradicting Malcev and the finite residual `<z^2>`.

**Consequences and limits.**
- Let `A_0(N)` be the least mass of a detecting cycle on `Y_(Gamma/N)`, with `nu >= nu_0(zeta) > 0`
  (`nu_0 = 1/3` for `zeta` a primitive cube root of unity). Monomial models over `Gamma/N` have
  defect at least `4 nu_0 / A_0(N)`. `A_0` can only decrease when `N` is enlarged, since detecting
  cycles push forward.
- `A_0(N) >= (sys(N) - 1)/(2 max_r |r|)`, where `sys(N)` is the least word length of a nontrivial
  element of `N`: a smaller cycle lifts to the Cayley complex, where `k` vanishes on all integral
  2-cycles. So `A_0 -> infinity` along shrinking `N`, and `(MCF1)` never gives a dimension-free floor
  by itself.
- At `g >= 3`, for normal quotients, `(MCF1)` beats the Frobenius floor `delta d^(-1/2)` exactly when
  `A_0(N) = o([Gamma : N]^(1/2))`.
- The mechanism is abelian. Along a detecting cycle, monomial holonomy is a scalar at each vertex, and
  the `d` deck translates give `d` independent quantized tests. A general unitary tuple has no such
  per-vertex holonomy: products of commutators of unitaries are arbitrary determinant-one unitaries,
  so a single cycle only sees the determinant.
