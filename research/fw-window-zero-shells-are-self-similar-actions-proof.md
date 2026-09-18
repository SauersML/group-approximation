---
rg: 2
id: fw-window-zero-shells-are-self-similar-actions-proof
kind: route
title: Enumerate the rays for one direction; for the other, transfix the graph of s^m and keep the points with infinite forward orbit
target: fw-window-zero-shells-are-self-similar-actions
requires:
  - fw-inputs-admit-no-twisted-shell-normalization
  - fw-descending-shift-power-windows-force-torsion-centre
  - fw-inputs-fail-commuting-shell-windows
  - fw-shell-inputs-at-window-zero-are-highly-transitive
  - fp-window-group-makes-shell-germ-group-fp
---

Notation as in the target.

**Item 1.** Let `Y = {y_1, …, y_m}`, `R_i = {σ^k(y_i) : k >= 0}` and `F = X − ⋃ R_i`, which is
finite.
- The `R_i` are disjoint infinite rays, since `σ` is injective and `y_i ∉ σ(X)`.
- `σ(F) ⊆ F`. Suppose `σ(x) = σ^k(y_i)` with `x ∈ F`. Then `k = 0` is impossible because
  `y_i ∉ σ(X)`, and `k >= 1` gives `x = σ^(k-1)(y_i)` by injectivity. So `σ` permutes the
  finite set `F`.
- Enumerate `X`: first the points of `F`, then `σ^k(y_i)` at position `|F| + mk + (i-1)`.
- In this enumeration `σ` adds `m` on every position `>= |F|`, so it is near equal to `s^m`.
- Hence `s^m ρ_g s^-m = σ ρ_g σ^-1 = ρ_(ψ(g))` on `σ(X) = X − Y`, which is cofinite.
- For `m = 1` this is the inclusion `s ρ(P) s^-1 <= ρ(P)`, that is, window zero with `ε = -1`.
  `fp-window-group-makes-shell-germ-group-fp`, with `ε = -1`, `N = 0` and `W = ρ(P) ≅ P`, gives
  `R_ρ ≅ P *_ψ`. When `P` is finitely presented, `W` is finitely presented, and so is `Q_ρ`.
- That proof uses only that the elements of the window group are permutations of `N`, so it
  applies to genuine actions. This transfer is noted here and is not separately reviewed.

**Item 2.** Step 1 of `fw-descending-shift-power-windows-force-torsion-centre-proof`, which
transfixes the graph of `s^m` under the twisted action `(ρ_g, ρ_(ψ(g)))`, gives:
- a cofinite `ρ(P)`-invariant `N_1`;
- an injection `s' : N_1 -> N`, near equal to `s^m`, with `s'(ρ_g x) = ρ_(ψ(g)) s'(x)`;
- an orbit graph consisting of `m` forward rays through all large `n` and finitely many
  finite components.

Let `X = {x ∈ N_1 : s'^j(x) is defined for every j}`.
- **`X` is `ρ(P)`-invariant.** For `x ∈ X` and `g ∈ P`, induction gives
  `s'^j(ρ_g x) = ρ_(ψ^j(g)) s'^j(x)`, and every point involved lies in the `ρ(P)`-invariant
  `N_1`.
- **`X` is cofinite:** it contains the rays.
- **`σ = s'|_X`** maps `X` into `X` injectively.
- **`Y = X − σ(X)` has `m` points.** Since `σ` is near equal to `s^m` on the cofinite `X`,
  `|X ∩ [0,M]| − |σ(X) ∩ [0,M]| = m` for large `M`.
- **`Y` is `ψ(P)`-invariant,** because `σ(X)` is `ρ(ψ(P))`-invariant and `X` is `ρ(P)`-invariant.
- The rays from the points of `Y` are the `m` rays of the orbit graph. Every other point of `X`
  lies on a finite cycle.
- `ψ` is injective because `ρ` is injective into `NearSym(N)`.
- Infinite supports on the cofinite `X` are inherited.

**Items 3 to 5.** These are the cited nodes, applied as stated.
- Item 4 is Steps 1 to 3 of `fw-inputs-fail-commuting-shell-windows-proof`, in either
  direction.
- The descending case then gives a self-similar action of `[P,P]` of defect `N+1`, by item 2
  applied to the finite-index FW subgroup `[P,P]`.

**The verdict.** Combine items 1 to 4 with the centre statement of item 5.
- `St_N(R_L)` has `Z ⊇ K_2(N,R_L) ≅ Q^x` (`k2-central-in-steinberg-groups-of-leavitt-resolvent-ring`),
  and it is perfect, so `[P,P] = P`.
- `E_N(R_L)` has the central scalars `Q^x I_N`.
- Deligne's lattice has an infinite cyclic centre.

Each of these centres has infinite exponent, which item 5 forbids.
