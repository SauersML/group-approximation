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
* **Homogeneous actions of arithmetic lattices (sofic, dead as candidates).** The
  canonical free mixing action `SL_n(Z) ↷ SL_n(R)/SL_n(Z)` is sofic for every
  `n >= 2` (`sl3z-lattice-space-action-is-sofic`). The points with finite orbit are
  the images of the commensurator. Mixing of `SL_n(Q_p)` on the S-arithmetic cover
  makes the Hecke orbits equidistribute, and
  `finite-equidistributed-orbits-give-sofic-action` gives finite models. So mixing
  does not obstruct soficity when periodic orbits equidistribute, and route
  `mixing-nonsofic-action-from-sl3z-lattice-space-action` can never fire. The
  surviving explicit candidate is `SL_3(Z) ↷ SL_3(R)/Λ` with `Λ` cocompact, which
  has no finite orbits (`sl3z-on-cocompact-lattice-quotient-is-not-sofic`, route
  `mixing-nonsofic-action-from-sl3z-cocompact-quotient`).
  *Update (ex-sl3z-cocompact-quotient, 2026-09-13).* Benoist--Quint equidistribution makes the Hecke
  mechanism universal. In any simple real Lie group, a Zariski-dense sofic subgroup with infinitely many
  finite orbits on a lattice quotient acts soficly (`hecke-orbits-make-lattice-quotient-actions-sofic`). So
  every commensurability class of arithmetic lattices is dead as a source of candidates. What survives
  is cross-class pairs and non-arithmetic lattices acting on their own quotients. For the cross-class
  candidate, soficity is equivalent to the existence of topological microstates
  (`uniquely-ergodic-action-sofic-iff-topological-microstates`). Honest finite actions are uniformly
  excluded (`sl3z-cocompact-quotient-uniformly-far-from-finite-actions`). Nonsoficity would follow from
  `sl3z-is-stable-in-finite-actions` together with
  `sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions`.
* **Containment seeds (solve-sofic-actions, 2026-09-13).** `free-action-containing-nonsofic-group-relation-is-nonsofic`
  supplies seeds without subgroups: a lattice of a Howe--Moore group with one free action whose restricted
  orbit relation contains a free action of a nonsofic group has a nonsofic action, hence a free mixing one by
  `howe-moore-lattice-nonsofic-action-transfers-to-mixing`. Bernoulli actions of simple Kazhdan nonsofic groups
  cannot seed a sofic host (`simple-kazhdan-bernoulli-relation-hosts-contain-the-group`,
  `leavitt-unit-bernoulli-relations-have-no-sofic-host`).
* **Seeds that are not simple Kazhdan groups (solve-sl3z-nonsofic-seed, 2026-09-13).**
  `rigid-bernoulli-seed-relations-embed-their-group-in-the-host` extends the Bernoulli no-go to every group
  with a wq-normal infinite Kazhdan subgroup. That includes the Kun--Thom wreaths and every group containing
  one.
  `kun-thom-actions-have-no-host-without-p-torsion` shows that the nonsofic Kun--Thom relations of Theorem E
  pairs sit in no free action of a group without infinite elementary abelian `p`-subgroups. That covers every
  lattice of `SL_3(R)`, every finitely generated linear group in characteristic `0`, `F_2 × F_2`, and the
  torsion-free tree-product lattices.
  So for these hosts, containment seeds must be non-malleable free actions of nonsofic groups.
