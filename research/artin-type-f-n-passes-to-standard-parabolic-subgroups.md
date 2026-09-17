---
rg: 2
id: artin-type-f-n-passes-to-standard-parabolic-subgroups
kind: claim
title: "If an Artin group is of type F_n, so is every standard parabolic subgroup"
distinct_from:
  artin-k-pi-1-passes-to-standard-parabolic-subgroups: that passes asphericity of the Salvetti complex down to parabolic subgroups; this passes the finiteness length of the group down, with no asphericity assumed.
  artin-type-f-n-reduces-to-free-of-infinity-graphs: that passes type F_n up from free-of-infinity parabolic subgroups; this passes it down to all standard parabolic subgroups.
  retracts-of-type-f-groups-are-of-type-f: that is about algebraic retracts; a standard parabolic subgroup is in general not an algebraic retract, only a coarse (1-Lipschitz) retract.
---

Let `Γ` be a finite Coxeter graph on `S`, let `T ⊆ S`, and let `n ∈ {1, 2, …} ∪ {∞}`.
If `A_Γ` is of type `F_n`, then the standard parabolic subgroup `A_T = A_{Γ_T}` is of
type `F_n`.

**Why this is not already recorded.** The dead attempt "Subgroups, quotients,
retractions" in `every-free-of-infinity-artin-group-is-type-f-infinity` notes that the
Godelle–Paris retraction `Sal(Γ) → Sal(Γ_T)` is only `W_T`-equivariant and that
restricting homotopy modules to an infinite-index subgroup loses finite generation. That is
correct for the modules, but the group-level statement still holds: the retraction lifts to
the universal covers, and on vertex sets it is a 1-Lipschitz retraction `r : A_Γ → A_T`
for the word metrics in the standard generators. Brown's criterion on Rips complexes then
transfers `F_n` from `A_Γ` to `A_T`.

**Consequences.**

- The class of Coxeter graphs whose Artin group is of type `F_n` is closed under induced
  subgraphs; failure of `F_n` is upward closed. With
  `artin-type-f-n-reduces-to-free-of-infinity-graphs` this gives the exact two-sided
  reduction `artin-f-n-iff-maximal-free-of-infinity-parabolics-f-n`.
- A counterexample to Zaremsky Problem 1.5 that is minimal for induced subgraphs has every
  proper standard parabolic subgroup of type `F_∞`.

Proof: route `artin-type-f-n-passes-to-standard-parabolic-subgroups-proof`. It uses the
Godelle–Paris retraction with the explicit cell formula of Charney–Paris
(arXiv:1401.7634, Theorem 2.5 and Lemma 2.6, read from the LaTeX source 2026-09-17) and
K. S. Brown's filtration criterion (J. Pure Appl. Algebra 44 (1987), Corollary 3.3; cited, not
re-read). The same Lipschitz map is J. M. Alonso's quasi-retract setting (J. Pure Appl.
Algebra 95 (1994)); the proof below does not rely on that paper.
