---
rg: 2
id: nuclear-factor-with-infinite-mf-tensor-exists
kind: claim
title: Some separable nuclear C*-algebra with a faithful trace has an infinite spatial tensor product with an MF algebra
distinct_from:
  nuclear-algebra-without-uct-exists: that is the negation of the UCT problem; this is one sufficient certificate for it, shaped like Ozawa's example with the non-exact factor R replaced by a nuclear algebra carrying a faithful trace.
  stw99-problem-ix1-nuclear-faithful-trace-quasidiagonal: that asks whether nuclear algebras with faithful traces are quasidiagonal; this asks for a tensor-infiniteness certificate, which by mf-min-tensor-exact-mf-is-mf refutes it.
  hyperfinite-factor-not-quasidiagonal: that has the non-exact R as second factor; this needs a nuclear second factor, and the natural leg algebra of that example is not nuclear (ozawa-leg-algebra-carries-non-amenable-trace).
artifacts:
  - research/artifacts/uct-fresh-mf-tensor-route-2026-09-12.md
---

**OPEN.** There are a separable MF C\*-algebra `A` and a separable nuclear
C\*-algebra `C` with a faithful tracial state such that `A ⊗_min C` is not stably
finite.

Route `nuclear-non-uct-via-infinite-mf-tensor`:
- such a `C` is not MF (`mf-min-tensor-exact-mf-is-mf`);
- so it fails the UCT (`tww-gabe-schafhauser-af-embedding-theorem`);
- which establishes `nuclear-algebra-without-uct-exists`.

This turns the UCT problem into an infiniteness question for tensor products,
the kind of statement Ozawa's Kazhdan-projection method already produces with R
as second factor. The only change needed is that the second factor be nuclear.

## Attempts

- **Ozawa's construction as printed.** The right legs of his proper isometry use
  the block representation of `SL(3,Z)`, whose generated algebra `D` is not
  nuclear (`ozawa-leg-algebra-carries-non-amenable-trace`). A nuclear subalgebra
  of R containing `D` would force `D` to be exact.
  - Decided, dead: `D = C*(⊕_k π_k(SL(3,Z)))` is not exact
    (`kazhdan-fd-block-representation-algebras-are-not-exact`, a Wassermann-type
    Kazhdan-projection certificate). So no nuclear algebra contains `D` or `D̄`.
  - The minimal slice algebra is the wrong object. The right slices of the Kazhdan
    projection `q` lie in the nuclear ideal `⊕_k B(H̄_k)` (block norms `≤ 1/d_k`),
    yet `q ∉ M ⊗_min ⊕_k B(H̄_k)`. See
    research/artifacts/uct-ozawa-leg-exactness-2026-09-12.md §4.
- **Nuclear second factor.** Dead as formulated. The spectral-gap projection is
  formed from `Σ_s σ(s) ⊗ π̄(s)`, and any second factor containing that element
  contains `π̄(G) ⊃` a copy of `D̄`, which is not exact. What survives is a second
  factor containing no copy of `π̄(G)`, reached by a different construction of the
  infinite projection. The certificate does not reach such a factor, and for it
  exactness plus a faithful trace would already give this claim.
