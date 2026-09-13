---
rg: 2
id: mixing-free-nonsofic-action-of-sofic-group
kind: claim
title: Some sofic group has a mixing free p.m.p. action that is not sofic
root: true
distinct_from:
  kun-thom-free-nonsofic-action: that is a free nonsofic action which is ergodic but never mixing, since it has the generalized Bernoulli action over G/Γ with infinite stabilizers as a factor; this asks for a mixing one, which no fixed-point-algebra argument can reach
  sofic-groups-in-paunescu-sofic-action-class: that is the refuted universal statement; this is the sharper residual question about the most chaotic actions
---

**OPEN.** There is a countable sofic group `G` and an essentially free, mixing
p.m.p. action `G ↷ (X,μ)` that is not sofic (Păunescu Definition 1.4).

## Why this is the residual question

Every nonsofic p.m.p. action of a sofic group recorded in this graph comes from
Kun--Thom Theorem C: a Kazhdan infranormal subgroup `Γ` whose fixed algebra
`L^∞(X)^Γ` is not `G`-invariant. `Γ` is infinite, so a mixing action has
`L^∞(X)^Γ = C`. Mixing passes to factors and to restrictions to infinite
subgroups, so the obstruction cannot be imported through either.
`kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions` makes this precise:
for any sofic embedding of such an action, the embedded algebra is orthogonal to
the normalized fixed algebra `D_𝒰^(σ(Γ))` beyond the constants.
`permutation-centralizer-blind-to-weakly-mixing-actions` does the same for
Theorem 4.1.

It can be imported through orbit equivalence. By
`howe-moore-lattice-nonsofic-action-transfers-to-mixing`, any ergodic nonsofic
action of a lattice in a Howe--Moore group yields a free mixing nonsofic action of
the same lattice.

So a mixing counterexample needs either a mechanism that works on mixing actions
themselves, or a nonsofic seed for a group with such an orbit-equivalence transfer.
Bernoulli shifts of sofic groups are sofic (Păunescu Section 2), so it cannot be
a Bernoulli shift.

## Attempts

* **Fixed-point algebras of Kazhdan subgroups.** Dead:
  `kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions` shows Theorem C's
  conclusion holds automatically when `Γ` acts ergodically, and the algebra
  Proposition 3.1 normalizes is orthogonal to the embedded action beyond the
  constants. No contradiction can come out of that algebra.
* **Co-induction from a subgroup.** `sofic-action-class-commensurability-proof`
  transfers nonsoficity from a subgroup action to the ambient group, but it needs
  a nonsofic seed and supplies no mixing: a mixing nonsofic seed is exactly what
  is missing.
* **Permutation centralizers (Kun--Thom Theorem 4.1).** Dead for everything the
  action forces into the embedding:
  `permutation-centralizer-blind-to-weakly-mixing-actions` proves that on a free
  action where `Γ` acts weakly mixingly, the permutations of the embedded crossed
  product commuting with `σ(Γ)` are exactly `σ(C_G(Γ))`. So Theorem 4.1 yields only
  Theorem B. Route `mixing-nonsofic-action-via-permutation-centralizers` is
  invalidated. Centralizing permutations outside the embedded crossed product are
  not forced by the action.
* **Orbit-equivalence transfer through a Howe--Moore envelope (live).**
  `howe-moore-lattice-nonsofic-action-transfers-to-mixing`: if `Γ <= H` is a lattice
  and `H` has the Howe--Moore property, an ergodic nonsofic seed `Z` gives the free
  mixing nonsofic action `Γ ↷ H ×_Γ (Z × {0,1}^Γ)`. It is orbit equivalent to
  `Γ ↷ Γ\H × Z'`, which has `Z` as a factor. Routes
  `mixing-nonsofic-action-from-simple-lattice-nonsofic-action` and
  `mixing-nonsofic-action-from-sl3z-nonsofic-action`. Dies at: no lattice of a
  Howe--Moore group is known to have a nonsofic action
  (`simple-group-lattice-admits-nonsofic-action`).
* **Products of two trees (live, conditional; ex-tree-lattice-mixing, 2026-09-13).**
  `nonsofic-infinitely-transitive-tree-lattice-gives-mixing` gives `F_2 × F_2` a free mixing
  nonsofic action from any nonsofic cocompact lattice whose projection closures are locally
  `∞`-transitive with finite `H^(∞)`-index. Routes: `mixing-nonsofic-action-from-f2xf2-mixing-action`
  through `f2xf2-admits-mixing-nonsofic-action`, and `mixing-nonsofic-action-from-tree-product-lattice`.
  The seed is `nonsofic-infinitely-transitive-tree-lattice`, which every nonsofic one-vertex
  square complex group supplies (Burger–Mozes Theorem 6.5). Radu's BMW lattice cannot seed
  an induced mixing action (`radu-lattice-induced-actions-are-never-mixing`). Dies at: no
  nonsofic lattice in a product of trees is known.
