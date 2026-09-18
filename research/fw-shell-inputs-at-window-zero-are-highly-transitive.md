---
rg: 2
id: fw-shell-inputs-at-window-zero-are-highly-transitive
kind: claim
title: If an FW input passes the window-zero shell gate in the other direction, it acts highly transitively on finitely many cofinite orbits; so it has trivial centre, and E_N(R_L) never passes
distinct_from:
  fw-inputs-admit-no-twisted-shell-normalization: that kills window zero in the direction s^-1 rho(P) s <= rho(P) outright; this treats the other direction s rho(P) s^-1 <= rho(P) and shows it forces high transitivity instead.
  faithful-pair-finite-steinberg-actions-need-noncentral-k2: that uses central K_2 to exclude pair-finite faithful actions of St_N(R_L); this uses trivial centre, forced by high transitivity, to exclude window-zero shell actions of St_N(R_L) when K_2 is central.
  genuine-action-shell-envelopes-generalize-the-regular-shell: that sets up genuine-action shells and their gates; this constrains their window-zero case for FW inputs.
  fw-inputs-admit-no-twisted-normalizing-genuine-shell-action: that, from lane bh-kazhdan-inputs, excludes the direction s rho(P) s^-1 <= rho(P) only for automorphism twists and leaves non-surjective endomorphisms open; this treats every endomorphism in that direction and shows that it forces high transitivity with trivial centre.
---

**ESTABLISHED** by `fw-shell-inputs-at-window-zero-are-highly-transitive-proof` (lane
proof, elementary, not independently reviewed; no novelty claimed for the ingredients).

## Statement

Let `P ≠ 1` have property FW, and let `ρ : P -> Sym(N)` be an action in which every
`ρ_g`, `g ≠ 1`, has infinite support. Let `s : n ↦ n+1`. Suppose there is an endomorphism
`ψ : P -> P` with

    s ρ_g s^-1 = ρ_(ψ(g))   in NearSym(N), for every g ∈ P.

This is the window-zero gate `s ρ(P) s^-1 <= ρ(P)`, direction `ε = -1`. Then:

1. **Finitely many orbits.** There are `p >= 1` and infinite `P`-orbits `O_0, …, O_(p-1)`
   whose union is cofinite in `N`.
2. **High transitivity.** `P` acts highly transitively on each `O_r`. More precisely,
   `ψ^p(P)` fixes a point `y_r ∈ O_r`, and `(O_r − {y_r}, ρ∘ψ^p)` is isomorphic to
   `(O_r, ρ)` as `P`-sets.
3. **Normal structure.** Every normal subgroup of `P` acts on each `O_r` either trivially
   or transitively. A normal subgroup acting trivially on every `O_r` is trivial. In
   particular `Z(P) = 1`, and `P` has no nontrivial finite normal subgroup.

## Consequences

- **Both directions of window zero.** The other direction is dead for every FW input
  (`fw-inputs-admit-no-twisted-shell-normalization`). So an FW input with a nontrivial
  centre, or a nontrivial finite normal subgroup, passes neither direction of window zero
  for any action with infinite supports.
- **`E_N(R_L)`, `N >= 4`, never passes window zero.**
  - It has property (T), as a quotient of `St_N(R_L)`
    (`steinberg-finite-presentation-and-kazhdan-theorem`), so it has FW.
  - Its centre contains `λ I_N` for `λ ∈ Q^x`
    (`leavitt-tuples-make-rational-scalar-powers-elementary`, with `d = 2`), so it is
    nontrivial.
- **`St_N(R_L)`, `N >= 4`: window zero needs non-central `K_2`.**
  - If some action with infinite supports passes window zero, the direction is `ε = -1`,
    and item 3 gives `Z(St_N(R_L)) = 1`.
  - If `K_2(N,R_L)` were central, `Z(St_N(R_L))` would contain `π^-1(Q^x I_N) ≠ 1`, by item
    1 of `faithful-pair-finite-steinberg-actions-need-noncentral-k2`.
  - So window zero for `St_N(R_L)` forces `K_2(N,R_L)` to be non-central. Together with
    `k2-central-in-steinberg-groups-of-leavitt-resolvent-ring` it would be dead.
- **Other Kazhdan inputs.** The same holds for every Kazhdan input with nontrivial
  centre. One example is Deligne's lattice (`deligne-universal-cover-lattice-is-non-rf-kazhdan`).

## Scope

- Windows `N >= 1` are not treated.
- An FW input with trivial centre that carries a self-similar highly transitive action as
  in item 2 is not excluded.
- Inputs without FW are not constrained. `GL_n(Q)` lacks FW
  (`sl-n-q-lacks-property-fw`), so a shell input containing it can avoid FW.
