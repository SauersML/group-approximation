---
rg: 2
id: deligne-bounded-rank-monomial-models-need-large-detecting-cycles
kind: claim
title: A monomial sector model of a Deligne cover over Gamma/N with m defective relator coordinates has [Gamma:N] <= m A for every detecting 2-cycle of mass A
distinct_from:
  deligne-monomial-cover-models-have-a-detecting-cycle-floor: that bounds the normalized HS defect below by 4 nu / A by spreading the quantized curvature over a detecting cycle; this counts defective coordinates on the deck translates, which gives a rank bound linear in A and independent of nu.
---

**ESTABLISHED** (`deligne-bounded-rank-monomial-count-proof`). Unreviewed.

**Setting.** Notation of `deligne-monomial-cover-models-have-a-detecting-cycle-floor`: a monomial
model over a finite `Gamma`-set `X` has `rho(z) = zeta I`, `rho(s) = D_s P_s` with an exact action
`P`, relator values `rho(r~(S)) zeta^(-k_r)`, and the 2-complex `Y_X` with cells `(x, r)`. Put

```text
m = sum_(r in R) rank( rho(r~(S)) zeta^(-k_r) - I ),
```

the number of **defective cells**: the relator values are diagonal, so `m` counts the cells `(x, r)`
whose holonomy differs from `zeta^(k_r)`.

**Theorem.**
1. **Normal quotients.** If `X = Gamma/N` with `N` normal of finite index, every detecting integral
   2-cycle `Sigma` on `Y_X` gives

   ```text
   [Gamma : N] <= m |Sigma|_1,       so   [Gamma : N] <= m A_0(N).                (MRC1)
   ```

2. **Transitive quotients.** If `X = Gamma/Lambda` and `N` is the normal core of `Lambda`, then
   `[Gamma : Lambda] <= m A_0(N)`.
3. **Any finite `Gamma`-set.** With orbits `X_i` and cores `N_i`, `|X| <= m max_i A_0(N_i)`, and
   every orbit carries a defective cell.

**Consequences.**
- **Bounded-rank monomial models.** If each relator defect has rank at most `k`, then `m <= k |R|`.
  So a bounded-rank monomial sector model over `Gamma/N` needs the **detecting density**
  `alpha(N) = A_0(N) / [Gamma : N]` to be at least `1 / (k |R|)`. The normalized floor of the
  companion node gives only `[Gamma : N] <= k A_0(N)^2 / (4 nu^2)`.
- **Transfer upper bound.** If `N <= N_0` and `[N_0 : N]` is prime to the order of `zeta`, the
  transfer of a detecting cycle on `Y_(Gamma/N_0)` detects on `Y_(Gamma/N)`. So
  `A_0(N) <= [N_0 : N] A_0(N_0)`, i.e. `alpha(N) <= alpha(N_0)`, and `alpha` is bounded along such
  towers. Monomial models cannot be excluded by index alone.
- **The sharp question.** Bounded-rank monomial sector models over a family of normal quotients
  exist only if `alpha(N)` stays bounded below along it. So `alpha(N) -> 0` along principal
  congruence quotients, which would follow from detecting surface cycles of mass `o([Gamma : N])`,
  would exclude them over those quotients at every rank. The arithmetic-surface heuristic in
  `research/artifacts/deligne-sector-floor-2026-09-13-part2.md` (mass about `m^3` against index
  about `m^(dim Sp_(2g))`) predicts exactly that. It is unchecked.
- **Scope.** The count uses the deck group of `Gamma/N` and per-vertex scalar holonomy. General
  unitary tuples have neither.
