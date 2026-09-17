---
rg: 2
id: atomic-irs-strict-designs-are-nonsurjunctive-quotients-proof
kind: route
title: Identify the Schreier graph of an atomic subgroup with layered copies of its normalizer quotient
target: atomic-irs-strict-designs-are-nonsurjunctive-quotients
requires: []
artifacts:
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
---

Complete direct proof: artifact Sections 2 and 3.

1. **Atom.** All conjugates of an atom have equal mass, so the class is finite and ergodicity makes
   `mu` uniform on it. `N = N_Gamma(H)` has finite index `k`, hence `Q = N/H` is finitely
   generated. All conjugates give isomorphic Schreier graphs `X = H\Gamma`, and the root runs over all
   vertices. So `mu` carries a design iff `X` has `sigma tau = id` with `tau` not surjective
   (Lemma 2.1).
2. **(=>)** `nH . Hg = Hng` is a free left action of `Q` commuting with the right action. With
   `Gamma = disjoint union of N g_i`, the map `(nH, i) -> H n g_i` identifies `X` with `Q x {1..k}`.
   Shape-dependent automata commute with label-preserving automorphisms. So `tau` is a continuous
   `Q`-equivariant map of `(A^k)^Q`, hence a cellular automaton by Curtis-Hedlund-Lyndon. It is
   injective and not surjective.
3. **(<=)** Take a strict pair over `Q` with a cellular left inverse (Lemma 2.2: a continuous inverse
   on the compact image reads a finite window). For lifts `m_s in N`, `H n g_i . g_i^-1 m_s g_i = H n m_s g_i`.
   This does not depend on the choices, because `n m_s` normalizes `H`. The layer of `v` is
   `Stab(v)` among `k` distinct conjugates, and finitely many membership tests detect it in a bounded
   ball. Reading `x(v . g_i^-1 m_s g_i)` on layer `i` makes the pair act as the strict pair on every
   layer.
4. **Corollary.** Lemma 2.3 reduces a non-surjunctive group to a finitely generated `F_r/N`. Apply
   step 3 to `delta_N`.
