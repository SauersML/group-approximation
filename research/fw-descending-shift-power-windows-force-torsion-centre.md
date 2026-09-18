---
rg: 2
id: fw-descending-shift-power-windows-force-torsion-centre
kind: claim
title: If a shift power conjugates an FW input's action into itself in the descending direction, the centre of the input has finite exponent; so commuting shell windows fail in both directions for St_N(R_L)
distinct_from:
  fw-shell-inputs-at-window-zero-are-highly-transitive: that treats the single shift s and concludes high transitivity with trivial centre; this treats every power s^m and concludes that central elements have bounded finite order.
  fw-window-zero-descending-sign-forces-trivial-core: that treats s and concludes the endomorphism core acts finitarily; this treats s^m and constrains the centre.
  fw-inputs-fail-commuting-shell-windows: that closes commuting windows in the direction eps = 1; this closes them in the direction eps = -1 for inputs whose derived subgroup has a centre of infinite exponent.
  fw-inputs-admit-no-twisted-normalizing-genuine-shell-action: that closes the direction m > 0 toward the singular point for every twist, and the other direction for automorphisms; this handles the other direction for endomorphisms and every m.
---

**ESTABLISHED** by `fw-descending-shift-power-windows-force-torsion-centre-proof` (lane
proof, elementary, not independently reviewed; no novelty claimed for the ingredients).

## Statement

Let `P` be a finitely generated group with property FW. Let `ρ : P -> Sym(N)` be an action
in which every `ρ_g`, `g ≠ 1`, has infinite support, and let `s : n ↦ n+1`. Suppose there
are `m >= 1` and an endomorphism `ψ` of `P` with

    s^m ρ_g s^-m = ρ_(ψ(g))   in NearSym(N), for every g ∈ P.

Then the centre `Z(P)` has finite exponent: some `e >= 1` has `z^e = 1` for every
`z ∈ Z(P)`.

## Consequences

- **Commuting windows, direction `ε = -1`.** Let the copies `c_0, c_(-1), …, c_(-N)`
  pairwise commute, and suppose `s ρ(P) s^-1 <= <c_0, …, c_(-N)>`. The argument of
  `fw-inputs-fail-commuting-shell-windows`, run in this direction, gives
  `s^(N+1) ρ(P') s^-(N+1) <= ρ(P')` for `P' = [P,P]`. So `Z(P')` has finite exponent.
- **`St_N(R_L)`.** Take `N >= 4`, so that `St_N(R_L)` has (T), hence FW.
  - `St_N(R_L)` is perfect, so `P' = P`.
  - Its centre contains `K_2(N,R_L) ≅ Q^x` (`k2-central-in-steinberg-groups-of-leavitt-resolvent-ring`,
    with `leavitt-resolvent-k2-stability-holds`), which has elements of infinite order.
  - So **commuting windows of every width fail in both directions for `St_N(R_L)`**, for
    every genuine action with infinite supports.
  - So does descending window zero for every shift power. Ascending window zero for every
    power is already dead.
- **Other inputs.** The same holds for every FW input `P` for which `Z([P,P])` has
  infinite exponent. One example is Deligne's lattice.

## Scope

Non-commuting windows `N >= 1` are not treated. The conclusion constrains only the centre.
An FW input with a torsion centre of bounded exponent, or trivial centre, is not excluded
by this node.
