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
  - Undecided: whether `C*(⊕_k π_k(SL(3,Z)))` is exact.
  - Heuristic against: its blocks come from the expander family of Schreier
    graphs on `P²(F_p)`, and uniform Roe algebras of box spaces of Kazhdan groups
    are not exact.
  - Also undecided: the minimal slice algebra of the isometry.
- **Nuclear second factor.** The spectral-gap projection `q` needs property (T)
  only for `G`. The obstruction is the second factor: it must contain blocks of
  the representation with trace weights `c^{-k}`, and the algebra those blocks
  generate is `D`. So this attempt reduces to the same exactness question.
