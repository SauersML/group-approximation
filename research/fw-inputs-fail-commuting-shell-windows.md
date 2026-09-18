---
rg: 2
id: fw-inputs-fail-commuting-shell-windows
kind: claim
title: An infinite finitely generated FW input fails every shell window, of any width, whose shifted copies pairwise commute
distinct_from:
  fp-window-group-makes-shell-germ-group-fp: that shows a finitely presented window group gives a finitely presented germ group, and suggests pairwise commuting copies with W = P^(N+1) as the cheapest positive shape; this shows that shape never passes the window inclusion for FW inputs.
  fw-inputs-admit-no-twisted-shell-normalization: that is window zero; this is every window width N >= 0 under a commutation hypothesis, which it reduces to window zero for the power s^(N+1).
  fw-inputs-admit-no-twisted-normalizing-genuine-shell-action: that is the window-zero statement for all shift powers s^m; this uses its m > 0 case, which is also proved here directly.
  fw-inputs-pass-window-zero-only-via-proper-self-embeddings: that constrains window zero through an index formula; this handles wider windows with commuting copies.
---

**ESTABLISHED** by `fw-inputs-fail-commuting-shell-windows-proof` (lane proof, elementary,
not independently reviewed; no novelty claimed for the ingredients).

## Statement

Let `P` be an infinite finitely generated group with property FW. Let `ρ : P -> Sym(N)` be
an action in which every `ρ_g`, `g ≠ 1`, has infinite support, and let `s : n ↦ n+1`. In
`NearSym(N)` put `c_j = s^j ρ(P) s^-j` and, for `N >= 0`, `W_N = <c_0, …, c_N>`.

Suppose that `c_i` and `c_j` commute elementwise in `NearSym(N)` for all
`0 <= i < j <= N`. Then

    s^-1 ρ(P) s  ⊄  W_N.

So the finite-window gate of `shell-ascending-gate-is-a-finite-window-inclusion`, in the
direction `ε = 1` and at width `N`, fails for every genuine shell action of an FW input
whose shifted copies commute.

## Why commuting copies were the natural candidate

`fp-window-group-makes-shell-germ-group-fp` says a positive example "does not need a new
finite presentation theorem". If the copies `c_0, …, c_N` pairwise commute and generate
their direct product, then `W = P^(N+1)` is finitely presented whenever `P` is. For FW
inputs, such as `St_N(R_L)`, `Sp_2n(Z)` (`n >= 2`) and `SL_n(Z)` (`n >= 3`), that shape
is now closed in direction `ε = 1`.

## Mechanism

- Shift invariance makes `c_(-1)` commute with `c_0, …, c_(N-1)`.
- Inside a product of pairwise commuting subgroups, that forces `c_(-1)` into `c_N` times
  a central subgroup.
- On the derived subgroup `P' = [P,P]` this gives
  `s^-(N+1) ρ(P') s^(N+1) <= ρ(P')`: window zero for the power `s^(N+1)`.
- `P'` has finite index and is FW, so window zero for a shift power fails.

## Scope

- **The other direction.** For `ε = -1`, with `c_(-j)` in place of `c_j`, the same
  argument gives `s^(N+1) ρ(P') s^-(N+1) <= ρ(P')`. This is the descending-sign window
  zero for `s^(N+1)`. It is closed for FW inputs with nontrivial centre only through the
  shift-power analogue of `fw-shell-inputs-at-window-zero-are-highly-transitive`, which is
  not proved here.
- **Non-commuting windows.** Windows whose copies do not commute are not treated.
