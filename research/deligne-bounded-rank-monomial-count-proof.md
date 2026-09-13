---
rg: 2
id: deligne-bounded-rank-monomial-count-proof
kind: route
title: Each deck translate of a detecting cycle carries a defective cell, and one cell meets at most mass-many translates
target: deligne-bounded-rank-monomial-models-need-large-detecting-cycles
requires: []
---

Notation of the target. Write `e(y -> s.y)` for the edge of `Y_X` and `omega~(e)` in `R` for a real
lift of the phase that `rho(s)` puts on it, so `rho(s) e_y = exp(2 pi i omega~(e)) e_(s.y)`
(inverse letters use `-omega~`).

**Step 1: holonomy and defective cells.** The action `P` is exact, so the loop reading `r~` at `x`
closes, and `rho(r~) e_x = exp(2 pi i h(x, r)) e_x` with `h(x, r) = sum` of `omega~` over the loop.
The relator value `rho(r~) zeta^(-k_r)` is diagonal with entries `exp(2 pi i (h(x,r) - theta k_r))`.
So its defect rank is the number of `x` with `h(x, r) - theta k_r` not in `Z`. Call those cells
**defective**; there are `m` of them.

**Step 2: a detecting cycle meets a defective cell.** For an integral 2-cycle
`Sigma = sum n_(x,r) (x, r)`, `sum n_(x,r) h(x, r) = sum_e omega~(e) c_e(partial Sigma) = 0` in `R`,
because `partial Sigma = 0` as an integral 1-chain. If no cell of `supp Sigma` is defective, every
`h(x,r) - theta k_r` is an integer, so `theta sum n_(x,r) k_r = - sum n_(x,r) (h(x,r) - theta k_r)`
is an integer and `nu(Sigma) = 0`. So a detecting cycle has a defective cell in its support.

**Step 3: deck translates (item 1).** Let `X = Gamma/N`, `N` normal. The group `Q = Gamma/N` acts on
`X` by right multiplication. The action is free and commutes with the left `Gamma`-action, so it
maps cells `(x, r)` to `(x g, r)`, edges to edges and integral cycles to integral cycles, preserving
the coefficient sum of each relator type and hence `nu`. Every translate `Sigma g` is detecting,
and by Step 2 contains a defective cell. So there are at least `|Q| = [Gamma : N]` pairs `(g, c)`
with `c` defective and `c` in `supp(Sigma g)`. For a fixed cell `c = (x, r)`, `c` lies in
`supp(Sigma g)` iff `(x g^(-1), r)` lies in `supp Sigma`. As `g` runs over `Q`, `x g^(-1)` runs over
`X` bijectively, so at most `|supp Sigma| <= |Sigma|_1` values of `g` qualify. Hence
`[Gamma : N] <= m |Sigma|_1`.

**Step 4: transitive quotients (item 2).** Let `X = Gamma/Lambda`, `N` its core, and
`p : Y_(Gamma/N) -> Y_(Gamma/Lambda)` the covering map, which is `[Lambda : N]`-to-one on cells.
Pushforward preserves integral cycles and `nu`, so `p_*(Sigma g)` is detecting on `Y_X` and meets a
defective cell of the model over `X` (Step 2 applies to it). Its support lies in `p(supp(Sigma g))`.
A cell `c` of `Y_X` has `[Lambda : N]` preimages, each meeting at most `|Sigma|_1` translates by
Step 3. So `[Gamma : N] <= m [Lambda : N] |Sigma|_1`, i.e. `[Gamma : Lambda] <= m |Sigma|_1`.

**Step 5: any finite `Gamma`-set (item 3).** Apply Step 4 on each orbit `X_i` with its own count
`m_i` of defective cells, `sum m_i = m`. Then `|X| = sum |X_i| <= sum m_i A_0(N_i) <= m max_i A_0(N_i)`.
If some `m_i = 0`, Step 2 would contradict the existence of detecting cycles on `Y_(Gamma/N_i)`
(item 4 of `deligne-monomial-cover-models-have-a-detecting-cycle-floor`), so every orbit carries a
defective cell.

**Step 6: consequences.**
- Rank at most `k` per relator gives `m <= k |R|`. The normalized floor `4 nu / A` against the
  normalized defect `2 (k/d)^(1/2)` gives only `d <= k A^2 / (4 nu^2)`.
- **Transfer.** For `N <= N_0`, spread each cell coefficient of a detecting `Sigma_0` on
  `Y_(Gamma/N_0)` to all `[N_0 : N]` preimages. Boundary commutes with this transfer, so it is a
  cycle of mass `[N_0 : N] |Sigma_0|_1`, with each relator coefficient sum multiplied by
  `c = [N_0 : N]`. If `zeta = exp(2 pi i j / q)` has order `q` and `gcd(c, q) = 1`, then
  `theta c sum n k_r` is not an integer when `theta sum n k_r` is not, so the transfer detects. ∎
