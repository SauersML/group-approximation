---
rg: 2
id: stw99-problem-lvii-kk-trace-classification
kind: claim
title: KK plus trace data classifies Z-stable nuclear algebras without the UCT (STW Problem LVII, Schafhauser Conjecture D)
root: true
distinct_from:
  stw99-problem-ii-nuclear-uct: that asks for the UCT itself; this asks whether classification can BYPASS it, replacing the total invariant by a unit-compatible KK-equivalence plus an affine identification of traces with the pairing condition.
artifacts:
  - research/artifacts/stw99-k1-kk-cluster-2026-08-30.md
---

**Problem LVII of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Schafhauser, Conjecture D): for `A, B` unital separable simple
nuclear `Z`-stable, does an invertible `κ ∈ KK(A,B)` preserving the
unit on `K_0`, together with an affine homeomorphism
`γ : T(B) → T(A)` compatible via `[γ(τ)] = [τ] ∘ κ`, force `A ≅ B`?
Schafhauser (Thm A) proves it when `(κ, γ)` are induced by an actual
unital *-homomorphism.

## Attempts

* The gap between Conjecture D and Theorem A is an existence theorem:
  realize an abstract compatible pair by a morphism.  Post-Szabo
  KK-uniqueness (`stw99-problem-lxii-kk-uniqueness` is now
  ESTABLISHED), the uniqueness half of the usual
  existence/uniqueness intertwining is unconditional, so Conjecture D
  reduces entirely to KK-existence against a possibly UCT-less
  target — precisely where `stw99-problem-iii-r-omega-uct` (the
  `R^ω`-UCT) enters for the trace side.  Wiring: III + LXII-style
  uniqueness is the modern route sketch; a failure of Conjecture D
  would produce two non-isomorphic classifiable-like algebras
  KK-equivalent compatibly, hence a UCT-violating phantom pair — so
  refuting LVII is at least as hard as refuting II on the nose.
