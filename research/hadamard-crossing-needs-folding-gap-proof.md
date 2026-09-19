---
rg: 2
id: hadamard-crossing-needs-folding-gap-proof
kind: route
title: Uncross an auxiliary-unfolded adversary with its mirror (submodularity of cuts), fill the non-folded locus with a random signed dictator, and cap the relaxed value by Martinsson Proposition 49(c)
target: hadamard-crossing-needs-folding-gap
requires:
  - hadamard-gadget-deletion-ratio-window
artifacts:
  - experiments/ugc-hadamard-gadget-k4-2026-09-17/hadk_mincut.py
  - experiments/ugc-hadamard-gadget-k4-2026-09-17/results-2026-09-19.txt
---

Items 1 and 2 of `hadamard-crossing-needs-folding-gap` are elementary. Its
`## Proof` section gives the proof in full, and the steps are summarized here.
Item 3 imports one proposition.

## Steps

1. **Mirror and uncross.** For a relaxed `f` with `S = {f = +1}`, define the
   mirror `f~(x) = -f(-x)`, with `S~ = -(S^c)`.
   * `f~` has the same pins as `f`.
   * `T = S ∩ S~`, `-T = (S ∪ S~)^c`, and `D = S Δ S~ = {f(x) = f(-x)}`
     partition `Q`.
2. **Fill.** Set `g = +1` on `T`, `-1` on `-T`, and `sigma x_i` on `D`, with
   `sigma` and `i` uniform.
   * `g` is folded and pinned, so its law is random on `P`.
   * Edge by edge, `E g-cut = (cut_T + cut_{S ∪ S~})/2 + [e ⊂ D]/K`.
3. **Submodularity.** Per edge,
   `cut_{S∩S~} + cut_{S∪S~} <= cut_S + cut_{S~}`, and
   `cut_{S~}(e) = cut_S(-e)`. Averaging over an optimal relaxed `mu` and using
   the edge symmetry `e -> -e` gives `z* <= z_U + eta_k/K`.
4. **Relaxed cap (import).** `K z_U(k) <= 2`. This is by LP duality and group
   averaging, which give a direction-balanced optimal weighting with
   completeness `1 - 2^(-k)`, followed by Martinsson's Proposition 49(c).
   * **Imported verbatim.** The import is the one recorded in
     `hadamard-gadget-deletion-ratio-window` item 5 and its proof route.
   * **Martinsson's Definition 28.** Martinsson (arXiv:2408.04832) defines
     the relaxation as follows: "relax the definition of the soundness by
     not requiring that the assignment A of the auxiliary variables Yk is
     folded. Note that the assignment A is still required to be folded on
     the primary variables Xk".
   * **Our adversary is exactly this.** Our relaxed adversary is folded
     exactly at the primaries `±chi_a` and free elsewhere, which is
     Martinsson's `rs`.
