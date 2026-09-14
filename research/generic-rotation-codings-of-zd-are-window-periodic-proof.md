---
rg: 2
id: generic-rotation-codings-of-zd-are-window-periodic-proof
kind: route
title: Rational perturbation of the rotation vector preserves the cell structure of a generic interval coding and gives exact periodic window models
target: generic-rotation-codings-of-zd-are-window-periodic
requires:
  - rf-subshifts-are-periodic-window-approximable
  - residually-finite-actions-give-matricial-crossed-products
  - steinberg-elementary-groups-are-simple-mod-centre
artifacts:
  - research/artifacts/sk-general-actions-b-converse-map-2026-09-13-part2.md
---

Full derivation: artifact §7.

1. **Cells.** For finite `W`, the points `β_i − ⟨w,α⟩` (`i < m`, `w ∈ W`) are pairwise distinct, by genericity and independence. The `W`-pattern of `x_t` is constant on each open arc they cut out, and `L_W(X)` is the set of arc labels. Let `η` be the least arc length and `C = max_(w ∈ W) |w|_1`.
2. **Free and minimal.**
   - Coding generic points gives an almost one-to-one factor map onto the minimal rotation, so the language is uniformly recurrent and `X` is minimal.
   - A period `v` of a point forces `⟨v,α⟩ ∈ Z`, so `v = 0`. So `X` is free.
3. **Rational perturbation.**
   - For `N > max(3/η, 3C/(2η))`, put `α' = round(Nα)/N`. The endpoints move by `< η/3`, so they keep their cyclic order, the arc labels are unchanged, and every arc is longer than `1/N`.
   - A shifted grid `t_0 + (1/N)Z` avoiding the endpoints meets every arc and is invariant under `t ↦ t + ⟨v,α'⟩`.
   - The `NZ^d`-periodic configurations `y_t(v) = col(t + ⟨v,α'⟩)` form a finite invariant subset of the window SFT `X_W` realizing all of `L_W(X)`.
4. **Residual finiteness.** `X` is perfect. `rf-subshifts-are-periodic-window-approximable` gives Kerr–Nowak residual finiteness.
5. **Groups.** `residually-finite-actions-give-matricial-crossed-products` makes the crossed product exactly matricial and `EL_N` LEF. `steinberg-elementary-groups-are-simple-mod-centre` and EJZ give that `EL_N/Z` is infinite, simple and Kazhdan. The crossed product is finitely generated (`Z^d` is finitely generated, `X` is a subshift, and `q` is finite). ∎
