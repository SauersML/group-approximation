---
rg: 2
id: heisenberg-in-nv-forces-drift-free-central-element
kind: claim
title: A Heisenberg or BS(1,k) subgroup of a Brin-Thompson group nV forces an infinite-order element with zero mean offset for every invariant measure
distinct_from:
  thompson-v-has-no-heisenberg-subgroup: that is the n = 1 obstruction, derived from the undistortion theorem of Bleak et al.; this is a necessary condition for Heisenberg and BS(1,k) subgroups of every nV, stated through invariant measures of the offset cocycle.
  thompson-v-cyclic-subgroups-are-undistorted: that imports undistortion for V_n; this proves that an element with a drifting invariant measure is undistorted in nV, and draws the consequence for distorted central elements.
---

**ESTABLISHED** by `heisenberg-in-nv-forces-drift-free-central-element-proof`
(unreviewed by a verifier lane as of 2026-09-13).

**The offset cocycle.** Let `C = {0,1}^ω`, let `n >= 1`, and let `g ∈ nV`. On
each rectangle `u_1C × ⋯ × u_nC` of a domain partition of `g`, the element acts
by `(u_1w_1, …, u_nw_n) ↦ (v_1w_1, …, v_nw_n)`. The **offset** of `g` at a point
`p` of that rectangle is `s_g(p) = (|v_1| − |u_1|, …, |v_n| − |u_n|) ∈ Z^n`. It
is well defined, locally constant, bounded, and satisfies the cocycle identity
`s_{gh}(p) = s_g(h(p)) + s_h(p)`.

For a `g`-invariant Borel probability measure `μ` on `C^n`, the **drift** is
`ρ_μ(g) = ∫ s_g dμ ∈ R^n`. Call `g` **drift-free** if `ρ_μ(g) = 0` for every
`g`-invariant probability measure `μ`.

**Theorem.** Let `n >= 1`.

1. *(Drift gives undistortion.)* Let `S ⊂ nV` be finite, `K = max_{σ∈S} sup_p |s_σ(p)|_∞`,
   and `g ∈ ⟨S⟩`. If `ρ_μ(g) ≠ 0` for some `g`-invariant `μ`, then
   `|g^N|_S >= N·|ρ_μ(g)|_∞ / K` for all `N >= 1`.
2. *(Heisenberg.)* If `a, b ∈ nV` and `c = [a,b]` has infinite order and commutes
   with `a` and `b`, then `c` is drift-free.
3. *(Baumslag–Solitar.)* If `x, t ∈ nV`, `x` has infinite order and
   `t x t^-1 = x^k` with `|k| >= 2`, then `x` is drift-free.
4. *(Consequence.)* Suppose every infinite-order element of `nV` has an invariant
   probability measure with nonzero drift. Then `nV` contains no `H_3(Z)`, no
   `BS(1,k)` with `|k| >= 2`, and no `GL_d(Z)` or `SL_d(Z)` with `d >= 3`.

**Calibration n = 1.** Revealing tree pairs (Brin; used by Bleak et al.,
arXiv:1107.0672, to prove undistortion in `V_n`) show that every infinite-order
element of `V` has an attracting periodic orbit with nonzero return offset. The
atomic measure on that orbit has nonzero drift, so item 4 recovers
`thompson-v-has-no-heisenberg-subgroup` for `V`. That dynamical fact is standard
and was not re-derived here; the graph's `V` obstruction rests on the imported
undistortion theorem instead.

**For n >= 2 the hypothesis of item 4 fails.** Callard and Salo construct an
element `f ∈ mV` of infinite order with `|f^N| = O(log^4 N)` for every `m >= 2`
(`brin-thompson-mv-contains-a-distortion-element`). By item 1, `f` is
drift-free. So metric undistortion cannot exclude `H_3(Z)`, `BS(1,k)` or
`GL_d(Z)` from `nV` when `n >= 2`. Items 2 and 3 remain necessary conditions: any
such subgroup needs a drift-free element in the right algebraic position, and
drift-free elements exist.

**What it does not give.** Drift-freeness is necessary for distortion, not
sufficient, and distortion does not by itself produce `H_3(Z)` or `SL_3(Z)`.
