---
rg: 2
id: simple-monomial-completions-kill-the-tree-action-kernel-proof
kind: route
title: Kill the tree-action kernel and exhibit the boundary representation of the quotient completion
target: simple-monomial-completions-kill-the-tree-action-kernel
requires: []
artifacts:
  - research/artifacts/bh-steinberg-hosts-2026-09-12.md
---

Section 3 of the artifact.

1. **Tree action.** `g(xw) = π_g(x) g|_x(w)` defines homomorphisms
   `P -> Sym(X^n)`. `N` is the intersection of their kernels, and `P/N` acts
   faithfully on a locally finite rooted tree, so it is residually finite.
2. **`N` is restriction-closed.** For `g in N`, `π_g = id` and
   `xw = g(xw) = x g|_x(w)`, so `g|_x in N`.
3. **The recursion descends.** `π_(gn) = π_g` and `(gn)|_x = g|_x n|_x` for
   `n in N`. So `P/N` inherits a wreath recursion `psi_bar`, and
   `O_psi / J = O_(psi_bar)` by presentations.
4. **Boundary representation.** Let `V` have basis `X^ω`. Put `s_x(w) = xw`,
   `s_x*(yw) = δ_(xy) w`, and let `g` act through the tree action.
   - The Leavitt relations hold, because each infinite word has one first letter.
   - `g s_x = s_(π_g(x)) g|_x`, which is the defining relation.
   - `N` acts trivially.

   So `O_(psi_bar)` has a nonzero unital representation, and `J` is proper.
5. **Simple case.** If `O_psi` is simple, `J = 0`. A group with no nontrivial
   finite quotient acts trivially on each finite level `X^n`, hence lies in `N`.
