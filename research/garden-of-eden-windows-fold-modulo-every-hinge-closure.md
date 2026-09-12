---
rg: 2
id: garden-of-eden-windows-fold-modulo-every-hinge-closure
kind: claim
title: Every Garden-of-Eden window folds modulo the hinge closure of every reverse-sufficient partition
distinct_from:
  strict-pairs-transfer-to-table-realizations: that folds a window pair under every homomorphism into a surjunctive group; this folds one modulo the normal closure of the hinge words of each reverse-sufficient partition of the design, a quotient over which only this design need be surjective, and so refines that folding and ties the window to the reverse hinges.
  strict-automaton-tables-present-an-invisible-window-difference: that places a sofic-invisible element on a window difference of the table group; this places a two-cell window difference inside the hinge closure of every minimal reverse partition, a subgroup contained in both the surjunctive and the sofic radical.
  two-cell-window-differences-die-in-host-abelianization: that is the abelian consequence for two-cell windows, vacuous on commutator windows; this is the exact nonabelian condition, which is meaningful on commutator windows.
artifacts:
  - research/artifacts/hinge-closure-window-folding-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

**ESTABLISHED** by `garden-of-eden-hinge-closure-folding-proof`.

Let a design `D = (A, S, M, nu, mu)` be realized over a group `H` with
`sigma tau = id`, and let `p in A^Omega` be a Garden of Eden for `tau` on a finite
window `Omega`. For a partition `P` of `M x S`, let `N_P(H)` be the normal closure of
its hinge words: `(m' s')^(-1)(m s)` for `(m,s) ~_P (m',s')`, and `m s` for cells in
the marked class.

**Theorem.** For every reverse-sufficient `P`, some `w, w' in Omega` with
`p(w) != p(w')` have `w^(-1) w' in N_P(H)`.

The design is surjective over `H/N_P(H)`, and a periodic lift would carry an
unfolded Garden of Eden back to `H`. The normal subgroups over whose quotient this one
design is surjective are exactly those containing `N_P(H)` for some minimal
reverse-sufficient `P`. Every kernel into a surjunctive group is one of them.

**Two-cell windows.** If `Omega = {1, d}`, then `p(1) != p(d)` and

```text
d in ⋂_(P minimal reverse sufficient) N_P(H)  ⊆  Rad_surj(H)  ⊆  Rad_sof(H),
```

where `Rad_surj(H)` is the intersection of the kernels of all homomorphisms into
surjunctive groups. So the reverse hinges of every minimal reverse partition must
normally generate a subgroup containing the window difference.

**Monolithic descent.** For a two-cell window there is `K ⊴ H` with `d notin K` such
that the realization over `H/K` is still strict with the same Garden of Eden on
`{1, dK}`, and every nontrivial normal subgroup of `H/K` contains `dK`. So `H/K` is
monolithic, and its monolith is the normal closure of the window difference.

**Scope.** Over a simple host every nontrivial hinge closure is the whole group, so
nothing beyond strictness follows there, for the Leavitt unit group in particular. The
theorem bites on canonical table groups, whose only relators are forced coincidences.
It is a class theorem and decides Gottschalk's conjecture for no group.

Proof: Section 1 of the artifact.
