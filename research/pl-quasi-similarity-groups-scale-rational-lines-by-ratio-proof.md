---
rg: 2
id: pl-quasi-similarity-groups-scale-rational-lines-by-ratio-proof
kind: route
target: pl-quasi-similarity-groups-scale-rational-lines-by-ratio
requires: []
---

Direct proof. Notation as in the claim: `D ≅ (Q,+)`, written additively when
convenient, and `t` normalizes `D`. Since `Aut(Q) = Q^x`, `t` acts on `D` as
multiplication by some `r in Q^x`. `D` is divisible, so it maps trivially to
`Z/2` (orientation). Every element of `D` preserves orientation, and every
element has roots of every order inside `D`, which commute with it.

**Step 0: `c(d) = 1` for every `d in D`.**
- Suppose `c(d) = λ ≠ 1`, say `λ > 1`. Then `d(x) - x = (λ-1)x + O(1)` tends to
  `±∞` as `x -> ±∞`. So `Fix(d)` is nonempty and compact; let `α = min Fix(d)`.
- Points just left of `α` are moved, so `d` has left slope `μ ≠ 1` at `α`, with
  `μ in P ∩ R_{>0}`. If the slope were `1`, `d` would be the identity on a left
  neighbourhood of `α`, and `α` would not be the minimum of `Fix(d)`.
- For each `k >= 1` let `e in D` with `e^k = d`. Then `e` commutes with `d`, so it
  maps `Fix(d)` onto itself. Being increasing, it fixes `α`, and it maps a left
  neighbourhood of `α` into one.
- The chain rule for one-sided derivatives gives `μ = (left slope of e at α)^k`.
  So `μ` is a `k`-th power in `P ∩ R_{>0}` for every `k`, contradicting (P1).
- `λ < 1` is symmetric.

**Step 1: translation number.**
- By Step 0 and (P3), each `d in D` commutes with a translation by some
  `L_d > 0`, so it is a lift of an orientation-preserving homeomorphism of
  `R/L_d Z`. Hence `τ(d) = lim_n (d^n(x) - x)/n` exists, and
  `|d^n(y) - y - nτ(d)| <= L_d` for all `y` and `n` (Poincaré).
- For commuting `d, e in D`: `(de)^n(x) - x = [d^n(e^n x) - e^n x] + [e^n x - x]`,
  so `|(de)^n(x) - x - n(τ(d)+τ(e))| <= L_d + L_e`. Thus `τ : D -> R` is additive,
  hence `Q`-linear: `τ(r·d) = r τ(d)`.

**Step 2: conjugation scales `τ` by `c(t)`.**
- Write `c = c(t)`. By (P2), `t(x) = cx + O(1)`, and so `t^-1(y) = y/c + O(1)`.
- For `d in D`:
  `t d^n t^-1 (x) - x = c·d^n(t^-1 x) + O(1) - x = c·(t^-1 x + nτ(d) + O(L_d)) - x + O(1) = c n τ(d) + O(1)`,
  with `O(1)` independent of `n`. Hence `τ(t d t^-1) = c(t) τ(d)`.

**Step 3: `τ` is not identically zero on `D`.**
- Suppose it is, and pick `d ≠ 1` in `D`, with period `L = L_d`. A lift with
  translation number `0` has a fixed point, so `Fix(d)` is nonempty,
  `L`-periodic, closed and not all of `R`.
- `d` has finitely many breakpoints per period, so `Fix(d) ∩ [0,L]` is a finite
  union of points and closed intervals. The set `E` of left endpoints of the
  (bounded) components of `R \ Fix(d)` is therefore discrete and `L`-periodic, with
  `N_0 >= 1` points per period, and it has order type `Z`.
- At each `α in E`, `d` moves the points just right of `α`, so its right slope
  `s_α(d)` lies in `(P ∩ R_{>0}) \ {1}`.
- Fix `k >= 1` and take `e in D` with `e^k = d`. Then `e` commutes with `d`, so it
  permutes the components of `R \ Fix(d)` in order and restricts to an
  order-preserving bijection of `E`, a shift by some `s` places.
- If `s ≠ 0`, then `e^j(α)` is at least `|js|` places from `α`, so
  `|e^j(α) - α| >= (|js|/N_0 - 1)L` and `|τ(e)| >= |s|L/N_0 > 0`. That contradicts
  `τ ≡ 0` on `D`.
- So `e` fixes every `α in E` and maps a right neighbourhood of `α` into one. The
  chain rule gives `s_α(d) = s_α(e)^k` with `s_α(e) in P ∩ R_{>0}`.
- As `k` is arbitrary, `s_α(d)` is a `k`-th power for all `k`, contradicting (P1).

**Step 4: conclusion.**
- `τ` is a nonzero `Q`-linear map `D ≅ Q -> R`, hence injective. So every
  nontrivial element of `D` has nonzero translation number and no fixed point.
- For `d ≠ 1`: `r τ(d) = τ(r·d) = τ(t d t^-1) = c(t) τ(d)` with `τ(d) ≠ 0`, so
  `r = c(t)`. ∎
